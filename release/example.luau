-- luau-disassembler server client example.
-- Run bin/luau-server.exe first. Default address: http://127.0.0.1:7331
--
-- This example intentionally accepts bytecode from your own code path instead of fetching it
-- from any game object. Only inspect bytecode you own or are allowed to inspect.

local SERVER_URL = "http://127.0.0.1:7331"

local HttpService = game:GetService("HttpService")

local function resolveRequest()
    if typeof(request) == "function" then
        return request
    end
    if typeof(http_request) == "function" then
        return http_request
    end
    if syn and typeof(syn.request) == "function" then
        return syn.request
    end
    if http and typeof(http.request) == "function" then
        return http.request
    end

    -- Studio fallback. Enable "Allow HTTP Requests" in Game Settings.
    return function(options)
        local responseBody
        local ok, result = pcall(function()
            if options.Method == "GET" then
                responseBody = HttpService:GetAsync(options.Url)
            else
                responseBody = HttpService:PostAsync(
                    options.Url,
                    options.Body or "",
                    Enum.HttpContentType.ApplicationJson,
                    false,
                    options.Headers or {}
                )
            end
        end)

        if not ok then
            error(result, 2)
        end

        return {
            StatusCode = 200,
            Body = responseBody,
        }
    end
end

local httpRequest = resolveRequest()

local BASE64_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

local function base64Encode(input)
    local output = table.create(math.ceil(#input / 3) * 4)
    local outIndex = 1

    for index = 1, #input, 3 do
        local b1 = string.byte(input, index) or 0
        local b2 = string.byte(input, index + 1) or 0
        local b3 = string.byte(input, index + 2) or 0
        local remaining = #input - index + 1

        local value = b1 * 65536 + b2 * 256 + b3
        local c1 = math.floor(value / 262144) % 64
        local c2 = math.floor(value / 4096) % 64
        local c3 = math.floor(value / 64) % 64
        local c4 = value % 64

        output[outIndex] = string.sub(BASE64_ALPHABET, c1 + 1, c1 + 1)
        output[outIndex + 1] = string.sub(BASE64_ALPHABET, c2 + 1, c2 + 1)
        output[outIndex + 2] = remaining >= 2 and string.sub(BASE64_ALPHABET, c3 + 1, c3 + 1) or "="
        output[outIndex + 3] = remaining >= 3 and string.sub(BASE64_ALPHABET, c4 + 1, c4 + 1) or "="
        outIndex += 4
    end

    return table.concat(output)
end

local function requestJson(method, path, body)
    local response = httpRequest({
        Url = SERVER_URL .. path,
        Method = method,
        Headers = {
            ["Content-Type"] = "application/json",
        },
        Body = body and HttpService:JSONEncode(body) or nil,
    })

    local statusCode = response.StatusCode or response.Status or 0
    local responseBody = response.Body or response.body or ""
    local decoded = HttpService:JSONDecode(responseBody)

    if statusCode < 200 or statusCode >= 300 then
        local message = decoded.error and decoded.error.message or responseBody
        error(("luau-server returned HTTP %d: %s"):format(statusCode, message), 2)
    end

    return decoded
end

local LuauDisassembler = {}

function LuauDisassembler.health()
    return requestJson("GET", "/health")
end

function LuauDisassembler.disassemble(rawBytecode)
    return requestJson("POST", "/disassemble", {
        bytecode = base64Encode(rawBytecode),
        options = {
            include_disassembly = true,
        },
    })
end

function LuauDisassembler.decompile(rawBytecode)
    return requestJson("POST", "/decompile", {
        bytecode = base64Encode(rawBytecode),
        options = {
            include_disassembly = false,
        },
    })
end

-- Replace this with bytecode from an authorized source.
local rawBytecode = nil

print("server health:", HttpService:JSONEncode(LuauDisassembler.health()))

if rawBytecode then
    local decompiled = LuauDisassembler.decompile(rawBytecode)
    print(decompiled.source)
else
    warn("Set rawBytecode to a Luau bytecode string before calling decompile/disassemble.")
end

return LuauDisassembler

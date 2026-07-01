--!nocheck
-- Decompile  game:GetService("ReplicatedFirst").neuron  through the luau-server,
-- then print a preview, copy the full source to the clipboard, and save it to a file.
--
-- PREREQUISITE — start the server first (from the release zip), e.g.:
--     luau-server.exe
--   For big obfuscated modules give it room (the neuron takes ~40s server-side):
--     set LUAU_SERVER_TIME_BUDGET_SECS=180   (Windows)  then run luau-server.exe
--
-- Run THIS script from your executor while in the game.

local SERVER     = "http://127.0.0.1:7331/decompile"
local OUTFILE    = "neuron_decompiled.luau"   -- saved under the executor's workspace/ folder
local PRINT_FULL = false                       -- true = dump the whole thing to console (35k+ lines!)
local PREVIEW    = 40                           -- lines to preview when PRINT_FULL is false

-- pick: first callable from a list of candidates (executors name things differently) ----------
local function pick(...)
	for _, fn in ipairs({ ... }) do
		if type(fn) == "function" then
			return fn
		end
	end
	return nil
end

-- 1) Resolve the target script ----------------------------------------------------------------
local rf = game:GetService("ReplicatedFirst")
local target = rf:FindFirstChild("neuron") or rf.neuron
assert(target, "ReplicatedFirst.neuron was not found (is it loaded yet?)")

-- 2) Get its compiled bytecode (executor API) -------------------------------------------------
local getbytecode = pick(getscriptbytecode, (syn and syn.getscriptbytecode), dumpstring)
assert(getbytecode, "your executor exposes no getscriptbytecode / dumpstring")
local bytecode = getbytecode(target)
assert(
	type(bytecode) == "string" and #bytecode > 0,
	"got empty bytecode (the script may not be loaded, or is compiled on demand)"
)

-- 3) Base64-encode it (the server takes base64) -----------------------------------------------
local b64enc = pick(
	(crypt and crypt.base64encode),
	(crypt and crypt.base64 and crypt.base64.encode),
	(crypt and crypt.base64_encode),
	(base64 and base64.encode),
	base64_encode,
	(syn and syn.crypt and syn.crypt.base64 and syn.crypt.base64.encode)
)
assert(b64enc, "your executor exposes no base64 encoder")

-- The standard base64 alphabet is JSON-safe, so build the body by hand — this avoids
-- HttpService:JSONEncode choking on a multi-megabyte string.
local body = '{"bytecode":"' .. b64enc(bytecode) .. '"}'

-- 4) POST to the server (executor HTTP API) ---------------------------------------------------
local httprequest = pick(
	(syn and syn.request),
	(http and http.request),
	http_request,
	request,
	(fluxus and fluxus.request)
)
assert(httprequest, "your executor exposes no http request function")

print(("[neuron] sending %d bytes of bytecode to %s ..."):format(#bytecode, SERVER))
local res = httprequest({
	Url = SERVER,
	Method = "POST",
	Headers = { ["Content-Type"] = "application/json" },
	Body = body,
})

local status = res and (res.StatusCode or res.status_code)
local respbody = res and (res.Body or res.body)
assert(
	status == 200,
	("server returned %s: %s\n(is luau-server.exe running on 127.0.0.1:7331? raise LUAU_SERVER_TIME_BUDGET_SECS if it timed out)")
		:format(tostring(status), tostring(respbody))
)

-- 5) Parse the JSON and pull out the decompiled source ----------------------------------------
local data = game:GetService("HttpService"):JSONDecode(respbody)
local source = data.source
assert(source and #source > 0, "no `source` field in the server response")
if data.partial then
	warn("[neuron] partial reconstruction — some regions are best-effort")
end

-- 6) Output: preview/print + clipboard + file -------------------------------------------------
if PRINT_FULL then
	print(source)
else
	local lines = string.split(source, "\n")
	for i = 1, math.min(PREVIEW, #lines) do
		print(lines[i])
	end
	if #lines > PREVIEW then
		print(("[neuron] ... (%d more lines — full source is in your clipboard and %s)"):format(#lines - PREVIEW, OUTFILE))
	end
end

local clip = pick(setclipboard, toclipboard, setrbxclipboard, set_clipboard, (Clipboard and Clipboard.set))
if clip then
	pcall(clip, source)
	print("[neuron] copied full source to clipboard")
else
	warn("[neuron] no clipboard function available on this executor")
end

if type(writefile) == "function" then
	pcall(writefile, OUTFILE, source)
	print(("[neuron] saved to workspace/%s (%d chars, %d lines)"):format(OUTFILE, #source, select(2, source:gsub("\n", "\n")) + 1))
end

print("[neuron] done.")

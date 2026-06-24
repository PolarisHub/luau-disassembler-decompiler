-- Multiple-value (multret) threading: a call/vararg that produces "to top" feeding the
-- next call's arguments (B=0), a multret return (B=0), and an open table constructor
-- (SETLIST C=0). Each must reconstruct the nested expression, not a `--[[...]]` marker.
local function triple()
	return 1, 2, 3
end

local function forward(...)
	return ... -- multret return of varargs
end

local a = math.max(triple()) -- f(g()): args to top
local packed = { triple() } -- open SETLIST: {g()}
print(triple()) -- statement call with multret args
local s = tostring(forward(7)) -- nested call

local function tail()
	return triple() -- multret return: return g()
end

return a, packed, s, tail

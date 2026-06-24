local function swap(a, b)
	return b, a
end
local function use()
	local x, y = swap(1, 2)
	local p, q, r = swap(x, y), 99
	return x, y, p, q, r
end
return use

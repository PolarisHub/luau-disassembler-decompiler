local function pick(a, b, c)
	local x = a and b
	local y = a or c
	local z = a and b or c
	local w = (a > 0) and "pos" or "nonpos"
	return x, y, z, w
end
return pick

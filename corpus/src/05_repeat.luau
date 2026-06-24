local function grow(n)
	local x = 1
	repeat
		x = x * 2
	until x > n
	return x
end
return grow

local function sumto(n)
	local total = 0
	for i = 1, n do
		total = total + i
	end
	for j = n, 1, -2 do
		total = total - j
	end
	return total
end
return sumto

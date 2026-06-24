local function countdown(n)
	local sum = 0
	while n > 0 do
		sum = sum + n
		n = n - 1
	end
	return sum
end
return countdown

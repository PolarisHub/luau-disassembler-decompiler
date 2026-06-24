local function makeCounter(start)
	local count = start
	local function increment(by)
		count = count + by
		return count
	end
	return increment
end
return makeCounter

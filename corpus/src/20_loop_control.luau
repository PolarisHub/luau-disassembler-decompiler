-- Early loop exits: `break` (conditional, compiled as a conditional jump straight to the
-- loop exit) and `continue` (skip to the next iteration). Both must come back as native
-- keywords, not goto/labels, and the result must recompile.
local function sum_positive(list, cap)
	local total = 0
	for i = 1, #list do
		local v = list[i]
		if v > cap then
			break -- conditional jump to the loop exit
		end
		if v < 0 then
			continue -- conditional jump to the loop's continue point
		end
		total = total + v
	end
	return total
end

local function first_match(items, target)
	for _, item in ipairs(items) do
		if item == target then
			return item
		end
		if item == nil then
			break
		end
	end
	return nil
end

return sum_positive, first_match

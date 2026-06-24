local function classify(n)
	if n > 0 then
		return "positive"
	elseif n < 0 then
		return "negative"
	else
		return "zero"
	end
end
return classify

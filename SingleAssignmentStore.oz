%=================================
% SingleAssignmentStore.oz
% Authors: Jaikishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

declare SAS SASIndex

SASIndex = {NewCell 0}

SAS = {Dictionary.new}

% Procedures

fun { CheckForLoopInSAS Val KeyToFind}
   case Val
   of reference(Key)
   then
      if {RetrieveFromSAS Key} == equivalence(KeyToFind)
      then true
      else false
      end
   else
      {Browse hi}
      false
   end
end


proc { BindRefToKeyInSAS Key RefKey}
   if {Dictionary.member SAS Key} then
      case {Dictionary.get SAS Key}
      of equivalence(Key) then
	 if Key == RefKey then skip %Self Loops
	 else {Dictionary.put SAS Key reference(RefKey)} end
      end
   else
      raise missingKey(Key) end
   end
end

proc { BindValueToKeyInSAS Key Val}
   if {Dictionary.member SAS Key} then
      local CurrentVal in
	 CurrentVal = {Dictionary.get SAS Key}
	 case CurrentVal
	 of equivalence(K)
	 then
	    if {CheckForLoopInSAS Val Key} == false then
	       {Dictionary.put SAS Key Val}
	    end
	 [] reference(NextKey)
	 then {BindValueToKeyInSAS NextKey Val}
	 else raise alreadyAssigned(Key Val CurrentVal) end
	 end
      end
   else
      raise missingKey(Key) end
   end
end

% Setters and Getters

fun { AddKeyToSAS}
   SASIndex := @SASIndex + 1
   {Dictionary.put SAS @SASIndex equivalence(@SASIndex)}
   @SASIndex
end

fun { RetrieveFromSAS Data}
   local Val in
      if {Dictionary.member SAS Data} then
	 Val = {Dictionary.get SAS Data}
	 case Val of reference(Key) then {RetrieveFromSAS Key}
	 else Val end
      else
	 raise missingKey(Data) end
      end
   end
end

/*
local X Y Z in
   X = {AddKeyToSAS}
   Y = {AddKeyToSAS}
   Z = {AddKeyToSAS}
   {BindRefToKeyInSAS X Y}
   {BindRefToKeyInSAS Y Z}
   {BindValueToKeyInSAS Z reference(X)}
   {Browse {RetrieveFromSAS X}}
   {Browse {RetrieveFromSAS Y}}
   {Browse {RetrieveFromSAS Z}}
end
*/
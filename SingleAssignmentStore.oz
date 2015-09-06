%=================================
% SingleAssignmentStore.oz
% Authors: Jai Kishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

declare SAS SASIndex

SASIndex = {NewCell 0}

SAS = {Dictionary.new}

% Procedures

proc {BindRefToKeyInSAS Key RefKey}
   {Dictionary.remove SAS Key}
   {Dictionary.put SAS Key reference(RefKey)}
end

proc {BindValueToKeyInSAS Key Val}
   {Dictionary.remove SAS Key}
   {Dictionary.put SAS Key Val}
end

% Setters and Getters

fun {AddKeyToSAS}
   SASIndex := @SASIndex + 1
   {Dictionary.put SAS SASIndex equivalence(@SASIndex)}
   @SASIndex
end

fun {RetrieveFromSAS Data}
   local Val in
	  Val = {Dictionary.get SAS Data}
	  case Val
	  of reference(Key) then {RetrieveFromSAS Key}
	  else Val end
   end
end

%=================================
% SingleAssignmentStore.oz
% Authors: Jaikishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

declare

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
      false
   end
end

fun {ResolveLinksInRecord R}
   local Aux in
      fun {Aux Pairs}
	 case Pairs
	 of nil then nil
	 [] H|T then
	    case H
	    of [literal(X) Y] then
	       case Y
	       of equivalence(Z) then [literal(X) reference(Z)]|{Aux T}
	       [] record|_ then [literal(X) {ResolveLinksInRecord Y}]|{Aux T}
	       else H|{Aux T}
	       end
	       else raise illegalRecordPair(H) end
	    end
	 end
      end
      
      case R
      of [record literal(N) P] then [record literal(N) {Aux P}]
      else raise illegalRecord(R) end
      end
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
   local CurrentVal in
      CurrentVal = {RetrieveFromSAS Key}
      case CurrentVal
      of equivalence(K)
      then
	 if {CheckForLoopInSAS Val K} == false
	 then
	    case Val
	    of record|_ then {Dictionary.put SAS K {ResolveLinksInRecord Val}}
	    else {Dictionary.put SAS K Val}
	    end
	 end
      else raise alreadyAssigned(Key Val CurrentVal) end
      end
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
	 case Val of reference(Key) then
	    {RetrieveFromSAS Key}
	 else Val end
      else
	 raise missingKey(Data) end
      end
   end
end


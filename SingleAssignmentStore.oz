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


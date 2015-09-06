%=======Interpreter for Oz=======
% Interpreter.oz
% Authors: Jai Kishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

\insert Unify.oz

declare SStack Pop Temp

SStack = {NewCell nil}

Temp = {NewCell nil}

proc {Push S}
   SStack := S|SStack
end

fun {Pop}
   case @SStack
   of nil then nil
   [] H|T then
	  SStack := T
	  H
   end
end

%=======Interpreter for Oz=======
% Interpreter.oz
% Authors: Jai Kishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

\insert Unify.oz

declare SStack Pop Temp Interpret

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

proc {Interpret AST}
   {Push semanticstack(statement:AST environment:env())}
   local Execute in
      proc {Execute}
         Temp := {Pop}
         if @Temp \= nil then
            case @Temp.statement
            of nil then skip
            [] [nop] then {Execute}
            end
         else skip
         end
      end
      {Execute}
   end
end

{Interpret [[nop] [nop] [nop]]}

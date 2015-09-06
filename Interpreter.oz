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

proc {CreateVar X Env S}
   local NewEnv in
      {AdjoinAt Env X {AddKeyToSAS} NewEnv}
      {Push semanticstack(statement:S environment:NewEnv)}
   end
end

proc {Bind X Y Env}
   case Y
   of [procedure Arg Statement] then
      ???
   else {Unify X Y Env}
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
            [] [localvar ident(X) S] then
               {CreateVar X @Temp.environment S}
               {Execute}
            [] [bind X Y] then
               {Bind X Y @Temp.environment}
               {Execute}
            [] X|Xs then
               if Xr \= nil then {Push semanticstack(statement:Xs environment:@Temp.environment)}
               else skip
               end
               {Push semanticstack(statement:X environment:@Temp.environment)}
               {Execute}
            end
         else skip
         end
      end
      {Execute}
   end
end

% ==> Logger/Check Statements
% {Browse @SStack}
% {Browse {Dictionary.toRecord _ SAS}}
% {Interpret [[nop] [nop] [nop]]}

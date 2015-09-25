%=======Interpreter for Oz=======
% Interpreter.oz
% Authors: Jai Kishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

\insert Unify.oz

declare SStack Temp PrintRoutine Push Pop Bind CreateVar Interpret Conditional Match Apply

SStack = {NewCell nil}
Temp = {NewCell nil}

proc {Push S}
   SStack := S|@SStack
end

fun {Pop}
   case @SStack
   of nil then nil
   [] H|T then
      SStack := T
      H
   end
end

proc {Bind X Y Env}
   case Y
   of [procedure Arg Statement] then
      {Unify X procedure(argument:Arg statement:Statement environment:Env) Env}
   else {Unify X Y Env}
   end
end

proc {CreateVar X Env Statement}
   local NewEnv in
      {AdjoinAt Env X {AddKeyToSAS} NewEnv}
      {Push semanticstack(statement:Statement environment:NewEnv)}
   end
end

proc {Conditional ident(X) S1 S2 Env}
   local Condition in
      Condition = {RetrieveFromSAS Env.X}
      if Condition == literal(true) then
         {Push semanticstack(statement:S1 environment:Env)}
      else
         if Condition == literal(false) then
            {Push semanticstack(statement:S2 environment:Env)}
         else
            raise booleanCheckFailed(X) end
         end
      end
   end
end

proc {Interpret AST}
   {Push semanticstack(statement:AST environment:env())}
   local Execute in
      proc {Execute}
	 {PrintRoutine}
	 Temp := {Pop}
	 if @Temp \= nil then
	    case @Temp.statement
	    of nil then {Browse 'Success'}
	    [] [nop] then {Execute}
	    [] [localvar ident(X) Xs] then
	       {CreateVar X @Temp.environment Xs}
	       {Execute}
	    [] [bind X Y] then
	       {Bind X Y @Temp.environment}
	       {Execute}
            [] [conditional ident(X) S1 S2] then
               {Conditional ident(X) S1 S2 @Temp.environment}
               {Execute}
            [] [match X Pat S1 S2] then
               {Match X Pat S1 S2 @Temp.environment}
               {Execute}
            [] apply|ident(X)|Param then
               {Apply X Param @Temp.environment}
               {Execute}
            [] X|Xs then
	       if Xs \= nil then
		  {Push semanticstack(statement:Xs environment:@Temp.environment)}
	       else skip
	       end
	       {Push semanticstack(statement:X environment:@Temp.environment)}
	       {Execute}
	    end
	 else {Browse 'Success'}
	 end
      end
      {Execute}
   end
end

proc {PrintRoutine}
   {Browse @SStack}
   {Browse {Dictionary.items SAS}}
end

% {Interpret [[nop] [nop] [nop]]}

{Interpret [localvar ident(x) [bind ident(x) literal(5)]]}

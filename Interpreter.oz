%=======Interpreter for Oz=======
% Interpreter.oz
% Authors: Jai Kishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

\insert Unify.oz

declare SStack Temp PrintRoutine Push Pop Bind CreateVar Interpret Conditional Match Apply PushPatternVarsToEnv CheckRecordIfCompletelyBound

SStack = {NewCell nil}
Temp = {NewCell nil}

proc {Push S}
   SStack := S|@SStack
end

fun {CheckRecordIfCompletelyBound R Env}
   local CheckRecord CheckPairs in
      fun {CheckRecord Xs Curr}
	 case Xs of [record literal(N) Pairs] then {CheckPairs Pairs Curr} end
      end
      
      fun {CheckPairs Xs Curr}
	 case Xs
	 of nil then Curr
	 [] H|T then
	    case H
	    of [literal(_) X] then
	       local XVal in
		  case X of ident(Y)
		  then XVal = {RetrieveFromSAS Env.Y}
		  else XVal = X
		  end
		  
		  case XVal
		  of equivalence(Key) then false
		  [] record|_ then {CheckPairs T {CheckRecord XVal Curr}}
		  else {CheckPairs T Curr}
		  end
	       end
	    else raise illegalRecordPair(H) end
	    end
	 end
      end
      {CheckRecord R true}
   end
end

fun {PushPatternVarsToEnv R Env}
   local PushRecord PushPairs in
      fun {PushRecord Xs Env}
	 case Xs of [record literal(N) Pairs] then {PushPairs Pairs Env} end
      end
      
      fun {PushPairs Xs Env}
	 case Xs
	 of nil then Env
	 [] H|T then
	    case H
	    of [literal(_) X] then
	       case X
	       of ident(Y) then
		  local NewEnv in
		     {AdjoinAt Env Y {AddKeyToSAS} NewEnv}
		     {PushPairs T NewEnv}
		  end
	       [] record|_ then {PushPairs T {PushRecord X Env}}
	       else {PushPairs T Env}
	       end
	    else raise illegalRecordPair(H) end
	    end
	 end
      end
      {PushRecord R Env}
   end
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

proc {Conditional X S1 S2 Env}
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


proc {Match X P S1 S2 Env}
   local XVal in
      XVal = {RetrieveFromSAS Env.X}
      %{Browse XVal}
      case XVal
      of equivalence(K) then raise unboundX(X) end
      [] [record literal(Name1) Pairs1] then
	 case P
	 of [record literal(Name2) Pairs2] then
	    if {CheckRecordIfCompletelyBound XVal Env} then
	       local NewEnv in
		  NewEnv = {PushPatternVarsToEnv P Env}
		  try
		     {Unify XVal P NewEnv}
		     {Push semanticstack(statement:S1 environment:NewEnv)}
		  catch E then
		    % {Browse howdy}
		     {Push semanticstack(statement:S2 environment:Env)}
		  end		     
	       end
	    else raise partiallyUnboundX(X) end
	    end
	 else
	    %{Browse p_is_not_a_record}
	    {Push semanticstack(statement:S2 environment:Env)}
	 end
      else
	% {Browse x_is_not_a_record}
	 {Push semanticstack(statement:S2 environment:Env)}
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
               {Conditional X S1 S2 @Temp.environment}
               {Execute}
	    [] [match ident(X) Pat S1 S2] then
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

% {Interpret [localvar ident(x) [bind ident(x) literal(5)]]}

%{Interpret [[localvar ident(x)	[[nop]  [localvar ident(y)[[bind ident(x) ident(y)] [localvar ident(x)[nop]]]]]]]}

{Interpret [localvar ident(x)
	    [
	     [localvar ident(y)
	      [
	       [bind literal(10) ident(y)]
	       [bind ident(x) [record literal(label) [[literal(f1) literal(1)] [literal(f2) ident(y)]] ] ]
	       [match ident(x) [record literal(label) [[literal(f1) ident(y)] [literal(f2) ident(z)]] ]	[localvar ident(x) [bind ident(x) ident(y)]] [nop] ]
	      ]
	     ]
	    ]
	   ]
}
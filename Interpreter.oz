%=======Interpreter for Oz=======
% Interpreter.oz
% Authors: Jai Kishan Rupani
%          Proneet Verma
%          Triveni Mahatha
%================================

\insert Unify.oz

declare MultiStack Temp CurrStack NewThread SuspendCounter

MultiStack = {NewCell nil}
Temp = {NewCell nil}
CurrStack = {NewCell nil}
NewThread = {NewCell nil}
SuspendCounter = {NewCell 0}

fun {AddFreshVariablesToEnv Xs Env}
   local AddFreshVarToEnv in
      fun {AddFreshVarToEnv V Env}
	 case V
	 of ident(X) then {AdjoinAt Env X {AddKeyToSAS}}
	 else raise illegalIdentifier(V) end
	 end
      end

      case Xs
      of nil then Env
      [] X|Xr then {AddFreshVariablesToEnv Xr {AddFreshVarToEnv X Env}}
      end
   end
end

fun {SubstituteIdentifiers Exp Env}
   case Exp
   of procedure|_ then Exp
   [] H|T then {SubstituteIdentifiers H Env}|{SubstituteIdentifiers T Env}
   [] ident(X) then
      if {Value.hasFeature Env X} == false
      then raise varNotDeclared(X) end
      end
      {RetrieveFromSAS Env.X}
   else Exp end
end


proc {BindFormalToActual FP FEnv AP AEnv}
   case FP
   of FH|FT then
      case AP
      of AH|AT then
	 {Unify FH {SubstituteIdentifiers AH AEnv} FEnv}
	 {BindFormalToActual FT FEnv AT AEnv}
      else raise illegalArity() end
      end
   else skip
   end
end

fun {CheckVarForFreeVars Xs Env Bound SoFar}
   case Xs
   of X|Xr then {CheckVarForFreeVars Xr Env Bound {CheckVarForFreeVars X Env Bound SoFar}}
   [] ident(X) then
      if {List.member ident(X) Bound} then SoFar
      else
	 if {Value.hasFeature SoFar X} then SoFar
	 else
	    if {Value.hasFeature Env X} then {AdjoinAt SoFar X Env.X}
	    else raise varNotDeclared(X) end
	    end
	 end
      end
   else SoFar
   end
end

fun {ComputeClosure Stmts Env Bound SoFar}
   case Stmts
   of nil then SoFar
   [] [nop] then SoFar
   [] [localvar ident(X) Xs] then {ComputeClosure Xs Env ident(X)|Bound SoFar}
   [] [bind X Y] then {CheckVarForFreeVars X Env Bound {CheckVarForFreeVars Y Env Bound SoFar}}
   [] [conditional ident(X) S1 S2] then
      if {List.member ident(X) Bound} then {ComputeClosure S2 Env Bound {ComputeClosure S1 Env Bound SoFar}}
      else
	 if {Value.hasFeature SoFar X} then {ComputeClosure S2 Env Bound {ComputeClosure S1 Env Bound SoFar}} %if already a free variable then proceed normally
	 else
	    if {Value.hasFeature Env X} then {ComputeClosure S2 Env Bound {ComputeClosure S1 Env Bound {AdjoinAt SoFar X Env.X} } }
	    else raise varNotDeclared(X) end
	    end
	 end
      end
   [] [match ident(X) Pat S1 S2] then
      if {List.member ident(X) Bound} then {ComputeClosure S1 {PushPatternVarsToEnv Pat Env} Bound {ComputeClosure S2 Env Bound SoFar}}
      else
	 if {Value.hasFeature SoFar X} then {ComputeClosure S1 {PushPatternVarsToEnv Pat Env} Bound {ComputeClosure S2 Env Bound SoFar}} %if already a free variable then proceed normally
	 else
	    if {Value.hasFeature Env X} then {ComputeClosure S1 {PushPatternVarsToEnv Pat Env} Bound {ComputeClosure S2 Env Bound {AdjoinAt SoFar X Env.X} } }
	    else raise varNotDeclared(X) end
	    end
	 end
      end
   [] apply|ident(X)|Param then
      if {List.member ident(X) Bound} then {CheckVarForFreeVars Param Env Bound SoFar}
      else
	 if {Value.hasFeature SoFar X} then {CheckVarForFreeVars Param Env Bound SoFar} %if already a free variable then proceed normally
	 else
	    if {Value.hasFeature Env X} then {CheckVarForFreeVars Param Env Bound {AdjoinAt SoFar X Env.X} }
	    else raise varNotDeclared(X) end
	    end
	 end
      end
   [] newthread|Xs then
      {ComputeClosure Xs Env Bound SoFar}
   [] X|Xs then
      if Xs \= nil then {ComputeClosure Xs Env Bound {ComputeClosure X Env Bound SoFar}}
      else {ComputeClosure X Env Bound SoFar}
      end
   end
end


fun {CheckRecordIfCompletelyBound R Env}
   local CheckRecord CheckPairs in
      fun {CheckRecord Xs Curr}
	 case Xs of [record N Pairs] then
	    local NN in
	       case N
	       of ident(Name) then NN = {RetrieveFromSAS Env.Name}
	       else NN = N
	       end
	       case NN
	       of literal(_) then {CheckPairs Pairs Curr}
	       else raise illegalRecord(Xs) end
	       end
	    end
	 else raise illegalRecord(Xs) end
	 end
      end

      fun {CheckPairs Xs Curr}
	 case Xs
	 of nil then Curr
	 [] H|T then
	    case H
	    of [N X] then
	       local NN in
		  case N of ident(Name) then NN = {RetrieveFromSAS Env.Name}
		  else NN = N
		  end
		  case NN
		  of literal(_) then skip
		  else raise illegalRecordPair(H) end
		  end
	       end

	       local XVal in
		  case X of ident(Y) then XVal = {RetrieveFromSAS Env.Y}
		  [] reference(Y) then XVal = {RetrieveFromSAS Y}
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
	 case Xs of [record N Pairs] then
	    local NN in
	       case N
	       of ident(Name) then NN = {RetrieveFromSAS Env.Name}
	       else NN = N
	       end

	       case NN
	       of literal(_) then {PushPairs Pairs Env}
	       else raise illegalRecord(Xs) end
	       end
	    end
	 else raise illegalRecord(Xs) end
	 end
      end

      fun {PushPairs Xs Env}
	 case Xs
	 of nil then Env
	 [] H|T then
	    case H
	    of [N X] then
	       local NN in
		  case N
		  of ident(Name) then NN = {RetrieveFromSAS Env.Name}
		  else NN = N
		  end
		  case NN
		  of literal(_) then skip
		  else raise illegalRecordPair(H) end
		  end
	       end

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

proc {Bind X Y Env}
   case Y
   of [procedure Arg Statements] then
      local Closure P in
	 Closure = {ComputeClosure Statements Env Arg env()}
	 P = [procedure Arg Statements Closure]
	 {Unify X P Env}
      end
   else {Unify Y X Env}
   end
end

proc {CreateVar X Env Statement SStack}
   local NewEnv in
      {AdjoinAt Env X {AddKeyToSAS} NewEnv}
      {Push semanticstack(statement:Statement environment:NewEnv) SStack}
   end
end

proc {Conditional X S1 S2 Env SStack}
   if {Value.hasFeature Env X} == false
   then raise varNotDeclared(X)	end
   end

   local Condition in
      Condition = {RetrieveFromSAS Env.X}
      case Condition
      of literal(true) then {Push semanticstack(statement:S1 environment:Env) SStack} 
      [] literal(false) then {Push semanticstack(statement:S2 environment:Env) SStack}
      [] equivalence(_) then raise suspendOnUnbound(X) end
      else raise booleanCheckFailed(X) end
      end
   end
end

proc {Apply F ActualParams Env SStack}
   local FVal in
      FVal = {RetrieveFromSAS Env.F}
      case FVal
      of equivalence(_) then raise unboundProcedure(F) end
      [] [procedure FormalParams Statements Closure] then
	 if {List.length FormalParams} \= {List.length ActualParams} then
	    raise illegalArity(found:{List.length ActualParams} expected:{List.length FormalParams}) end
	 end

	 local NewEnv in
	    NewEnv = {AddFreshVariablesToEnv FormalParams Closure}
	    {BindFormalToActual FormalParams NewEnv ActualParams Env}
	    {Push semanticstack(statement:Statements environment:NewEnv) SStack}
	 end
      else raise notAProcedure(var:F value:FVal) end
      end
   end
end

proc {Match X P S1 S2 Env SStack}
   local XVal in
      if {Value.hasFeature Env X} == false
      then raise varNotDeclared(X) end
      end

      XVal = {RetrieveFromSAS Env.X}
      case XVal
      of equivalence(K) then raise suspendOnUnbound(X) end
      [] [record Name1 Pairs1] then
	 case P
	 of [record Name2 Pairs2] then
	    if {CheckRecordIfCompletelyBound XVal Env} then
	       local NewEnv in
		  NewEnv = {PushPatternVarsToEnv P Env}
		  try
		     {Unify P XVal NewEnv}
		     {Push semanticstack(statement:S1 environment:NewEnv) SStack}
		  catch E then
		     {Push semanticstack(statement:S2 environment:Env) SStack}
		  end
	       end
	    else
	       raise suspendOnUnbound(X) end
	    end
	 else
	    {Push semanticstack(statement:S2 environment:Env) SStack}
	 end
      [] procedure|_ then raise illegalTypeInPatternMatching(X) end
      else % XVal is literal(_)
	 local NewEnv in
	    case P
	    of ident(Z) then
	       NewEnv = {AdjoinAt Env Z {AddKeyToSAS}}
	       {Unify P XVal NewEnv}
	       {Push semanticstack(statement:S1 environment:NewEnv) SStack}
	    [] XVal then {Push semanticstack(statement:S1 environment:Env) SStack}
	    else {Push semanticstack(statement:S2 environment:Env) SStack}
	    end
	 end
      end
   end
end

fun {Pop SStack}
   case @SStack
   of nil then nil
   [] H|T then
      SStack := T
      H
   end
end

proc {Push S SStack}
   SStack := S|@SStack
end

proc {PushToBack S SStack}
   SStack := {List.append @SStack [S]}
end


proc {Interpret AST}
   CurrStack:= nil
   {Push semanticstack(statement:AST environment:env()) CurrStack}
   {Push @CurrStack MultiStack}

   local Execute in
      proc {Execute SStack}
	 {PrintRoutine SStack}
	 Temp := {Pop SStack}
	 if @Temp \= nil then
	    case @Temp.statement
	    of nil then {Browse 'Thread execution completed'}
	    [] [nop]then
	       SuspendCounter := 0
	       {Execute SStack}
	    [] [localvar ident(X) Xs] then
	       {CreateVar X @Temp.environment Xs SStack}
	       SuspendCounter := 0
	       {Execute SStack}
	    [] [bind X Y] then
	       {Bind X Y @Temp.environment}
	       SuspendCounter := 0
	       {Execute SStack}
	    [] [conditional ident(X) S1 S2] then
	       try
		  {Conditional X S1 S2 @Temp.environment SStack}
		  SuspendCounter := 0
		  {Execute SStack}
	       catch E then
		  case E
		  of suspendOnUnbound(Variable) then
		     SuspendCounter := @SuspendCounter+1
		     {Push @Temp SStack}
		     {PushToBack @SStack MultiStack}
		     {Browse 'Thread suspended'}
		     if @SuspendCounter == {List.length @MultiStack}
		     then {Browse 'All threads suspended. Exiting...'}
		     else
			{Browse 'Scheduling Another Thread For Execution'}
			CurrStack := {Pop MultiStack}
			case @CurrStack
			of nil then {Browse 'No more threads to run. Exiting...'}
			else {Execute CurrStack}
			end
		     end
		  else
		     raise E end
		  end
	       end
	    [] [match ident(X) Pat S1 S2] then
	       try
		  {Match X Pat S1 S2 @Temp.environment SStack}
		  SuspendCounter := 0
		  {Execute SStack}
	       catch E then
		  case E
		  of suspendOnUnbound(Variable) then
		     SuspendCounter := @SuspendCounter+1
		     {Push @Temp SStack}
		     {PushToBack @SStack MultiStack}
		     {Browse 'Thread suspended'}
		     if @SuspendCounter == {List.length @MultiStack}
		     then {Browse 'All threads suspended. Exiting...'}
		     else
			{Browse 'Scheduling Another Thread For Execution'}
			CurrStack := {Pop MultiStack}
			case @CurrStack
			of nil then {Browse 'No more threads to run. Exiting...'}
			else {Execute CurrStack}
			end
		     end
		  else
		     raise E end
		  end
	       end
	    [] apply|ident(X)|Param then
	       {Apply X Param @Temp.environment SStack}
	       SuspendCounter := 0
	       {Execute SStack}
	    [] [newthread S] then
	       NewThread:= nil
	       {Push semanticstack(statement:S environment:@Temp.environment) NewThread}
	       {PushToBack @NewThread MultiStack}
	       SuspendCounter := 0
	       {Execute SStack}
	    [] X|Xs then
	       if Xs \= nil then
		  {Push semanticstack(statement:Xs environment:@Temp.environment) SStack}
	       else skip
	       end
	       {Push semanticstack(statement:X environment:@Temp.environment) SStack}
	       {Execute SStack}
	    end
	 else
	    {Browse 'Thread Execution Completed'}
	    {Browse 'Scheduling Another Thread For Execution'}
	    CurrStack := {Pop MultiStack}
	    case @CurrStack
	    of nil then {Browse 'No more threads to run. Exiting...'}
	    else
	       {Execute CurrStack}
	    end
	 end
      end
      CurrStack := {Pop MultiStack}
      case @CurrStack
      of nil then {Browse 'No more threads to run. Exiting...'}
      else {Execute CurrStack}
      end
   end
end

proc {PrintRoutine SStack}
   {Browse @SStack}
   {Browse {Dictionary.items SAS}}
end

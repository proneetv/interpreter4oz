Jaikishan Rupani - 12308
Proneet Verma - 12520
Triveni Mahatha - 12764

Points to note:-
1.) We haven't used the new Unify.oz. Also please note that we have made some changes in Unify.oz because we support reference(_) value and hence have added another case for the same in pattern matching of X as well as Y. 
2.) Also we have added an error check in substitute identifiers to check whether the descrived variable is truly present in the environment or not and have added another case to make sure a procedutre value is not substituted recursively since the code of a procedure must not be substituted.
3.) The syntax for records is [record literal(label)  [ [literal(f1) _] [literal(f2) _] ] ]  and not [record literal(label)  [literal(f1) _] [literal(f2) _] 
4.) Value of true is literal(true) and of false is literal(false) for conditionals
5.) W have supported record label and feature names as ident(_) as well provided they are already assigned a literal(_) val before the record is used,
 otherwise depending on whether a feature name is illegal or record label is we display an exception illegalRecordPair or illegalRecord respectively.
6.) procedure syntax in [procedure FP S] where second argument is the list of formal parameters.
7.) We also support pattern matching of X if it is bounded to some literal(_).
8.) Also we require all parts of a record X to be fully bounded for it to be pattern matched. This was to avoid cases where some attributes are unbounded in X. We throw proper exception in such a case.
9.) Since procedure values are not part of the pattern matching in Unify.oz, we assume procedure to be always the RHS in bind and LHS to be unbound. Even Y is not a procedure and X is, as long as Y is unbound the code executes successfully since we cannot unify a procedure with some bounded value. 
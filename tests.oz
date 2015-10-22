
\insert Interpreter.oz

/*{Interpret [[nop] [newthread [[nop]]] [nop]]}

{Interpret [localvar ident(x) [bind ident(x) literal(5)]]}

{Interpret [[localvar ident(x)	[[nop]  [localvar ident(y)[[bind ident(x) ident(y)] [localvar ident(x)[nop]]]]]]]}

{Interpret [localvar ident(x)
	    [
	     [localvar ident(y)
	      [
	       [bind ident(x) [record literal(label) [[literal(f1) literal(1)] [literal(f2) ident(y)]] ] ]
	      [bind literal(10) ident(y)]
	       [match ident(x) [record literal(label) [[literal(f1) ident(s)] [literal(f2) literal(10)]] ]	[newthread [localvar ident(x) [bind ident(x) ident(s)]]] [nop] ]
	      ]
	     ]
	    ]
	   ]
}

{Interpret [localvar ident(x)
	    [
	     [localvar ident(z)
	      [
	       [bind ident(x) [procedure [ident(y) ident(x)] [localvar ident(x)
							      [
							       [localvar ident(y)
								[
								 [bind ident(x) [record literal(label) [[literal(f1) literal(15)] [literal(f2) ident(y)]] ] ]
								 [bind literal(10) ident(y)]
								 [match ident(x) [record literal(label) [[literal(f1) ident(s)] [literal(f2) ident(z)]] ]
								  [localvar ident(x) [bind ident(x) ident(s)]] [nop] ]
								]
							       ]
							      ]
							     ]
			      ]
	       ]
	      ]
	     ]
	     [apply ident(x) literal(1) literal(2)]
	    ]
	   ]
}

{Interpret [localvar ident(x)
	    [localvar ident(y)
	     [localvar ident(z)
	      [
	       [bind ident(x) [record literal(label) [[literal(f1) ident(y)] [literal(f2) ident(z)]] ]]
	       [bind ident(x) [record literal(label) [[literal(f1) literal(2)] [literal(f2) literal(1) ]] ]]
	      ]
	     ]
	    ]
	   ]
}

{Interpret [localvar ident(foo)
	    [localvar ident(bar)
	     [
	      [bind ident(foo) [record literal(person) [[literal(name) ident(bar)]] ]]
	      [bind ident(bar) [record literal(person) [[literal(name) ident(foo)]] ]]
	      [bind ident(foo) ident(bar)]]
	    ]
	   ]
}

{Interpret
 [localvar ident(x)
  [
   [localvar ident(y)
    [
     [localvar ident(x)
      [
       [bind ident(x) ident(y)]
       [bind ident(y) literal(true)]
       [conditional ident(y) [nop] [bind ident(x) literal(true)] ]
      ]
     ]
     [bind ident(x) literal(35)]
    ]
   ]
  ]
 ]
}

{Interpret
 [localvar ident(foo)
  [localvar ident(result)
   [
    [bind ident(foo) literal(true)]
    [conditional ident(foo) [bind ident(result) literal(true)] [bind ident(result) literal(false)] ]
    [bind ident(result) literal(true)]]]]
}

{Interpret
 [localvar ident(foo)
  [localvar ident(result)
   [
    [bind ident(foo) literal(false)]
    [conditional ident(foo) [bind ident(result) literal(true)] [bind ident(result) literal(false)] ]
    [bind ident(result) literal(false)]
   ]
  ]
 ]
}

{Interpret
 [localvar ident(x)
  [
   [bind ident(x)  [procedure [ident(y) ident(x)] [nop]] ]
   [apply ident(x) literal(1) literal(2)]
  ]
 ]
}

{Interpret
 [localvar ident(x)
  [
   [bind ident(x) [procedure [ident(y) ident(x)] [nop]] ]
   [apply ident(x) literal(1) [record literal(label) [[literal(f1) literal(1)]] ] ]
  ]
 ]
}

{Interpret
 [localvar ident(foo)
  [localvar ident(bar)
   [
    [bind ident(foo) [record literal(person) [[literal(name) ident(foo)]] ] ]
    [bind ident(bar) [record literal(person) [[literal(name) ident(bar)]] ] ]
    [bind ident(foo) ident(bar)]
   ]
  ]
 ]
}


{Interpret
 [localvar ident(foo)
  [localvar ident(bar)
   [localvar ident(quux)
    [
     [bind ident(bar) [procedure [ident(baz)] [bind [record literal(person) [[literal(age) ident(foo)]] ] ident(baz)] ] ]
     [apply ident(bar) ident(quux)]
     [bind [record literal(person) [[literal(age) literal(40)]]] ident(quux)]
     [bind literal(42) ident(foo)]
    ]
   ]
  ]
 ]
}

{Interpret
 [localvar ident(foo)
  [localvar ident(result)
   [
    [bind ident(foo) [record literal(bar)  [[literal(baz) literal(42)]     [literal(quux) literal(314)]] ] ]
    [match ident(foo) [record literal(bar) [[literal(baz) ident(fortytwo)] [literal(quux) ident(pitimes100)]] ] [bind ident(result) ident(fortytwo)] [bind ident(result) literal(314)] ]
    [bind ident(result) literal(42)]
    [nop]
   ]
  ]
 ]
}

{Interpret
 [localvar ident(foo)
  [localvar ident(bar)
   [localvar ident(baz)
    [
     [bind ident(foo) ident(bar)]
     [bind literal(20) ident(bar)]
     [match ident(foo) ident(foo) [bind ident(baz) ident(foo)] [bind ident(baz) literal(f)] ]
    ]
   ]
  ]
 ]
}

{Interpret
 [localvar ident(foo)
  [localvar ident(bar)
   [localvar ident(baz)
    [localvar ident(result)
     [
      [bind ident(foo) ident(bar)]
      [bind ident(bar) literal(person)]
      [bind ident(baz) [record ident(bar) [[literal(1) literal(25)]] ] ]
      [match ident(baz) [record ident(foo) [[ident(bar) ident(quux)]] ] [bind ident(result) [record ident(quux) [[literal(1) literal(2)]] ]]       [bind ident(result) literal(f)]]
      [bind ident(result) [record literal(25) [[literal(1) literal(2)]] ] ] 
     ]
    ]
   ]
  ]
 ]
}
*/

/*
% Unify.oz doesn't check for the names of the records features whether they are same or not. Here is an example where it successfully unifies these two records
{Interpret
 [bind  [record literal(person) [[literal(age) literal(25)]]]  [record literal(person) [[literal(age2) literal(25)]]]    ]
}
*/


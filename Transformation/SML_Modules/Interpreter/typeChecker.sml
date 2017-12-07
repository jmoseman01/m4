(* =========================================================================================================== *)
exception runtime_error;
fun error msg = ( print msg; raise runtime_error );
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

fun getLabel (itree(inode(label,_), inf)) = label
  | getLabel _ = raise Fail("error - this should never occur")

(*==========================================expression==========================================*)
fun typeOf(  itree(inode("expr", _), 
                [
                    disjunction
                ]
             ),
        m
    ) = typeOf (disjunction, m)
  | typeOf(  itree(inode("disjunction", _), 
                [
                    disjunction
                ]
             ),
        m
    ) = typeOf (disjunction, m)
  | typeOf(  itree(inode("conjunction", _),
                [
                    conjunction
                ]
             ),
        m
    ) = typeOf (conjunction, m)
  | typeOf(  itree(inode("equalitytest", _),
                [
                    equalitytest
                ]
             ),
        m
    ) = typeOf (equalitytest, m)
  | typeOf(  itree(inode("disjunction", _), 
                [
                    disjunction1,
                    itree(inode("||",_), [] ),
                    conjunction1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(disjunction1,m0)
            val t2 = typeOf(conjunction1,m0)
        in
            if t1=t2 andalso t1=BOOL then BOOL else ERROR
        end
  | typeOf(  itree(inode("conjunction", _), 
                [
                    conjunction1,
                    itree(inode("&&",_), [] ),
                    equalitytest1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(conjunction1,m0)
            val t2 = typeOf(equalitytest1,m0)
        in
            if t1=t2 andalso t1=BOOL then BOOL else ERROR
        end
        
  | typeOf(  itree(inode("addsub", _),
                [
                    addsub
                ]
             ),
        m
    ) = typeOf (addsub, m)
  | typeOf(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("<",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(equalitytest1,m0)
            val t2 = typeOf(addsub1,m0)
        in
            if t1=t2 andalso t1=INT then BOOL else ERROR
        end
  | typeOf(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode(">",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(equalitytest1,m0)
            val t2 = typeOf(addsub1,m0)
        in
            if t1=t2 andalso t1=INT then BOOL else ERROR
        end
  | typeOf(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("<=",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(equalitytest1,m0)
            val t2 = typeOf(addsub1,m0)
        in
            if t1=t2 andalso t1=INT then BOOL else ERROR
        end
  | typeOf(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode(">=",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(equalitytest1,m0)
            val t2 = typeOf(addsub1,m0)
        in
            if t1=t2 andalso t1=INT then BOOL else ERROR
        end
  | typeOf(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("==",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(equalitytest1,m0)
            val t2 = typeOf(addsub1,m0)
        in
            if t1=t2 andalso t1<>ERROR then BOOL else ERROR
        end
  | typeOf(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("!=",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(equalitytest1,m0)
            val t2 = typeOf(addsub1,m0)
        in
            if t1=t2 andalso t1<>ERROR then BOOL else ERROR
        end
        
  | typeOf(  itree(inode("multdivmod", _),
                [
                    multdivmod
                ]
             ),
        m
    ) = typeOf (multdivmod, m)
  | typeOf(  itree(inode("addsub", _), 
                [
                    addsub1,
                    itree(inode("+",_), [] ),
                    multdivmod1
                ]
             ),
        m0
    ) = let 
            val t1 = typeOf(addsub1,m0)
            val t2 = typeOf(multdivmod1,m0)
        in
            if t1=t2 andalso t1=INT then INT else ERROR
        end
   
  | typeOf(  itree(inode("addsub", _), 
                [
                    addsub1,
                    itree(inode("-",_), [] ),
                    multdivmod1
                ]
             ),
        m0
    ) = let
		val t1 = typeOf(addsub1, m0)
		val t2 = typeOf(multdivmod1, m0)
	in
		if t1 = t2 andalso t1 = INT then INT else ERROR
        end 

        
  | typeOf(  itree(inode("unaryminus", _),
                [
                    unaryminus
                ]
             ),
        m
    ) = typeOf (unaryminus, m)
  | typeOf(  itree(inode("multdivmod", _), 
                [
                    multdivmod1,
                    itree(inode("*",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
		val t1 = typeOf(multdivmod1, m0)
		val t2 = typeOf(unaryminus1, m0)
	in
		if t1 = t2 andalso t1 = INT then INT else ERROR
        end

  | typeOf(  itree(inode("multdivmod", _), 
                [
                    multdivmod1,
                    itree(inode("div",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
		val t1 = typeOf(multdivmod1, m0)
		val t2 = typeOf(unaryminus1, m0)
	in
		if t1 = t2 andalso t1 = INT then INT else ERROR
        end 

    | typeOf(  itree(inode("multdivmod", _), 
                [
                    multdivmod1,
                    itree(inode("mod",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
		val t1 = typeOf(multdivmod1, m0)
		val t2 = typeOf(unaryminus1, m0)
	in
		if t1 = t2 andalso t1 = INT then INT else ERROR
        end 

        
  | typeOf(  itree(inode("exponent", _),
                [
                    exponent
                ]
             ),
        m
    ) = typeOf (exponent, m)
  | typeOf(  itree(inode("unaryminus", _), 
                [
                    itree(inode("-",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
		val t1 = typeOf(unaryminus1, m0)
	in
		if t1 = INT then INT else ERROR
	end

        
  | typeOf(  itree(inode("notexpr", _),
                [
                    notexpr
                ]
             ),
        m0
    ) = typeOf (notexpr, m0)
  | typeOf(  itree(inode("exponent", _), 
                [
                    notexpr1,
                    itree(inode("^",_), [] ),
                    exponent1
                ]
             ),
        m0
    ) = let
		val t1 = typeOf(notexpr1, m0)
		val t2 = typeOf(exponent1, m0)
	in
		if t1 = t2 andalso t1 = INT then INT else ERROR
        end 

        
   | typeOf(  itree(inode("factor", _),
                [
                    factor (*integer | boolean | <ids>*)
                ]
             ),
        m0
    ) = typeOf(factor, m0)
    
  | typeOf(  itree(inode("notexpr", _), 
                [
                    itree(inode("!",_), [] ),
                    notexpr1
                ]
             ),
        m0
    ) = let 
		val t1 = typeOf(notexpr1, m0)
	in
		if t1 = BOOL then BOOL else ERROR
	end 

        
    | typeOf(  itree(inode("factor", _), 
                [
                    itree(inode("(",_), [] ),
                    expr1,
                    itree(inode(")",_), [] )
                ]
             ),
        m0
    ) = typeOf(expr1,m0)
    | typeOf(  itree(inode("factor", _), 
                [
                    itree(inode("|",_), [] ),
                    expr1,
                    itree(inode("|",_), [] )
                ]
             ),
        m0
    ) = typeOf(expr1,m0)
    
  | typeOf(  itree(inode("integer", _), 
                [
                    value
                ]
             ),
        m0
    ) = INT
  | typeOf(  itree(inode("boolean", _), 
                [
                    value
                ]
             ),
        m0
    ) = BOOL
  | typeOf(  itree(inode("ids", _), 
                [
                    id (*identifier*)
                ]
             ),
        m0
    ) = getType(accessEnv(getLeaf(id),m0))
           
 | typeOf(  itree(inode("ids", _),
                [
                    id (*identifier*),
                    itree(inode("++",_), [] )
                ]
             ),
        m0
    ) = let
		val t1 = getType(accessEnv(getLeaf(id),m0))
	in
		if t1 = INT then INT else ERROR
	end

 | typeOf(  itree(inode("ids", _), 
                [
                    itree(inode("++",_), [] ),
                    id (*identifier*)
                ]
             ),
        m0
    ) = let
                val varname = getLeaf(id)
                val env1 = accessEnv(varname,m0)
		val t1 = getType(env1)
	in
		if t1 = INT then INT else ERROR
	end

        
 | typeOf(  itree(inode("ids", _), 
                [
                    id, (*identifier*)
                    itree(inode("--",_), [] )
                ]
             ),
        m0
    ) = let
		val t1 = getType(accessEnv(getLeaf(id),m0)) 
	in
		if t1 = INT then INT else ERROR
	end

 | typeOf(  itree(inode("ids", _),
                [
                    itree(inode("--",_), [] ),
                    id (*identifier*)
                ]
             ),
        m0
    ) = let
		val t1 = getType(accessEnv(getLeaf(id),m0))
	in
		if t1 = INT then INT else ERROR
	end

  | typeOf(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
  | typeOf _ = raise Fail("error in typeCheck.typeOf - this should never occur")



(*==========================================statement==========================================*)

fun typeCheck(  itree(inode("prog",_), 
                [ 
                    stmtList
                ]
             ),
        m
    ) = typeCheck(stmtList, m)
  | typeCheck( itree(inode("stmtList",_),
                [
                    stmt,
                    itree(inode(";",_), [] ),
                    stmtList
                ]
            ),
        m       
    ) = typeCheck( stmtList, typeCheck(stmt, m))
  | typeCheck( itree(inode("stmtList",_),
                [
                    epsilon
                ]
            ),
        m       
    ) = m
  | typeCheck( itree(inode("stmt",_),
                [
                    anyStmt
                ]
            ),
        m       
    ) = typeCheck(anyStmt, m)
  | typeCheck( itree(inode("dec",_),
                [
                    itree(inode("int",_), [] ),                 
                    id
                ]
            ),
        m      
    ) = updateEnv( getLeaf(id), INT, m )
  | typeCheck( itree(inode("dec",_),
                [
                    itree(inode("bool",_), [] ),                 
                    id
                ]
            ),
        m     
    ) = updateEnv( getLeaf(id), BOOL, m )
    | typeCheck( itree(inode("assign",_),
                [
                    id,
                    itree(inode("=",_), [] ),                 
                    expr0
                ]
            ),
        m       
    ) = 
        let 
		val t1 = typeOf(expr0,m)
		val t2 = getType(accessEnv(getLeaf(id),m))
	in
		if t1 = t2 then m else error "assign typecheck error"
	end    
  | typeCheck( itree(inode("increment",_),
                [
                    increment
                ]
            ),
        m
    ) = let
            val label = getLabel(increment)
        in
            if (label = "assign") then
                let
                    val m1 = typeCheck (increment, m)
                in
                    m1
                end
            else 
                let
                    val t1 = typeOf (increment, m)
                in
                    m
                end
        end
  | typeCheck( itree(inode("block",_),
                [
                    itree(inode("{",_), [] ),
                    stmtList1,                 
                    itree(inode("}",_), [] )
                ]
            ),
        m0
    ) = let
  		val m1 = typeCheck(stmtList1,m0)
  	in
  		m0
  	end
  | typeCheck( itree(inode("conditional",_),
                [
                    itree(inode("if",_), [] ),
                    expr1,                 
                    itree(inode("then",_), [] ),
                    block1
                ]
            ),
        m0
    ) = let
		val t = typeOf(expr1,m0)
		val m1=typeCheck(block1,m0)
	in
		if t = BOOL then m0 else error "if then failed type check"
	end

  | typeCheck( itree(inode("conditional",_),
                [
                    itree(inode("if",_), [] ),
                    expr,                 
                    itree(inode("then",_), [] ),
                    block1,
                    itree(inode("else",_), [] ),
                    block2
                ]
            ),
        m0
    ) = let
		val t = typeOf(expr,m0)
		val m1=typeCheck(block1,m0)
		val m2=typeCheck(block2,m0)
	in
		if t = BOOL then m0 else error "if then else failed type check"
	end

  | typeCheck( itree(inode("whileLoop",_),
                [
                    itree(inode("while",_), [] ),
                    itree(inode("(",_), [] ),
                    expr,
                    itree(inode(")",_), [] ),
                    block
                ]
            ),
        m0
    ) = let
		val t = typeOf(expr,m0)
		val m1=typeCheck(block,m0)
	in
		if t = BOOL then m0 else error "while loop failed type check"
	end

  (*<forLoop> ::= "for" "(" <assign> ";" <expr> ";" <increment> ")" <block> .*)
  | typeCheck( itree(inode("forLoop",_),
                [
                    itree(inode("for",_), [] ),
                    itree(inode("(",_), [] ),
                    assign1,
                    itree(inode(";",_), [] ),
                    expr,
                    itree(inode(";",_), [] ),
                    increment1,
                    itree(inode(")",_), [] ),
                    block1
                ]
            ),
        m
    ) = let
                val t=typeOf(expr,m)
                val m1=typeCheck(assign1,m)
                val m2=typeCheck(increment1,m)
                val m3=typeCheck(block1,m)
        in
                if t = BOOL then m else error "for loop failed type check"
        end

  | typeCheck( itree(inode("printStmt",_),
                [
                    itree(inode("print",_), [] ),
                    itree(inode("(",_), [] ),
                    expr,                 
                    itree(inode(")",_), [] )
                ]
            ),
        m0
    ) = let
            val t = typeOf(expr,m0)
        in
            if t <> ERROR  then m0 else error "failed print type check"
        end

  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)
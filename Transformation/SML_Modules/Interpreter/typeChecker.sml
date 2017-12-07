(* =========================================================================================================== *)
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
            val (v1, m1) = typeOf (disjunction1, m0)
        in
            if (v1 = (Boolean true)) then
                (v1, m1)
            else  	
                let 
                      val (v2, m2) = typeOf(conjunction1, m1)
                in
                (v2, m2)
                end
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
        val (v1, m1) = typeOf (conjunction1, m0)
        in
            if (v1 = (Boolean true)) then
                let 
                        val (v2, m2) = typeOf (equalitytest1, m1)
                in
                    (v2, m2)
                end
            else (v1, m1)
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
            val (v1, m1) = typeOf(equalitytest1, m0)
            val (v2, m2) = typeOf(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int < v2Int) then Boolean true (*compare v1 < v2*)
                         else Boolean false
        in
                (result, m2)
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
            val(v1, m1) = typeOf(equalitytest1, m0)
            val(v2, m2) = typeOf(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int > v2Int) then Boolean true (*compare v1 > v2*)
                         else Boolean false
        in
                (result, m2)
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
            val(v1, m1) = typeOf(equalitytest1, m0)
            val(v2, m2) = typeOf(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int <= v2Int) then Boolean true (*compare v1 <= v2*)
                         else Boolean false
        in
                (result, m2)
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
            val(v1, m1) = typeOf(equalitytest1, m0)
            val(v2, m2) = typeOf(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int >= v2Int) then Boolean true (*compare v1 >= v2*)
                         else Boolean false
        in
                (result, m2)
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
            val(v1, m1) = typeOf(equalitytest1, m0)
            val(v2, m2) = typeOf(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int = v2Int) then Boolean true (*compare v1 == v2*)
                         else Boolean false
        in
                (result, m2)
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
            val(v1, m1) = typeOf(equalitytest1, m0)
            val(v2, m2) = typeOf(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int <> v2Int) then Boolean true (*compare v1 != v2*)
                         else Boolean false
        in
                (result, m2)
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
            val(v1, m1) = typeOf(addsub1, m0)
            val(v2, m2) = typeOf(multdivmod1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int + v2Int;
            val result = Integer v3Int (*compute v1 + v2*)
        in
                (result, m2)
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
            val(v1, m1) = typeOf(addsub1, m0)
            val(v2, m2) = typeOf(multdivmod1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int - v2Int;
            val result = Integer v3Int (*compute v1 - v2*)
        in
                (result, m2)
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
            val(v1, m1) = typeOf(multdivmod1, m0)
            val(v2, m2) = typeOf(unaryminus1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int * v2Int;
            val result = Integer v3Int (*compute v1 * v2*)
        in
                (result, m2)
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
            val(v1, m1) = typeOf(multdivmod1, m0)
            val(v2, m2) = typeOf(unaryminus1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int div v2Int;
            val result = Integer v3Int (*compute v1 div v2*)
        in
                (result, m2)
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
            val(v1, m1) = typeOf(multdivmod1, m0)
            val(v2, m2) = typeOf(unaryminus1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int mod v2Int;
            val result = Integer v3Int (*compute v1 mod v2*)
        in
                (result, m2)
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
            val(v1, m1) = typeOf(unaryminus1, m0)
            val v1Int = getInt v1;
            val v2Int = ~v1Int;
            val result = Integer v2Int (*compute ~v1*)
        in
                (result, m1)
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
            val (v1, m1) = typeOf(notexpr1, m0)
            val (v2, m2) = typeOf(exponent1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = mypower(v1Int, v2Int);
            val result = Integer v3Int (*compute v1 power v2*)
        in
                (result, m2)
        end
        
   | typeOf(  itree(inode("factor", _),
                [
                    factor (*integer | boolean | <ids>*)
                ]
             ),
        m0
    ) = let
            val label = getLabel(factor)
        in
            typeOf (factor, m0)
        end
    
  | typeOf(  itree(inode("notexpr", _), 
                [
                    itree(inode("!",_), [] ),
                    notexpr1
                ]
             ),
        m0
    ) = let
            val (v1, m1) = typeOf(notexpr1, m0)
            val v1Bool = getBool v1;
            val v2Bool = not(v1Bool);
            val result = Boolean v2Bool (*compute !v1*)
        in
                (result, m1)
        end
        
    | typeOf(  itree(inode("factor", _), 
                [
                    itree(inode("(",_), [] ),
                    expr1,
                    itree(inode(")",_), [] )
                ]
             ),
        m0
    ) = let
            val (v1, m1) = typeOf(expr1, m0)
        in
                (v1, m1)
        end
    | typeOf(  itree(inode("factor", _), 
                [
                    itree(inode("|",_), [] ),
                    expr1,
                    itree(inode("|",_), [] )
                ]
             ),
        m0
    ) = let
            val (v1, m1) = typeOf(expr1, m0)
            val v1Int = getInt v1;
            val v2Int = if (v1Int > 0) then v1Int else ~v1Int 
            val result = Integer v2Int
        in
                (result, m1)
        end
  (*| typeOf(  itree(inode("factor", _), 
                [
                    expr1 (*integer | boolean | <ids>*)
                ]
             ),
        m0
    ) = typeOf(expr1, m0) removed for now because duplicate*)
    
  | typeOf(  itree(inode("integer", _), 
                [
                    value
                ]
             ),
        m0
    ) = let
            (*val v1 = Integer 1 need to do some more work*)
            val intString = getLeaf(value)
            val v1Int = valOf(Int.fromString(intString))
            val v1 = Integer v1Int
        in
            (v1, m0)
        end
  | typeOf(  itree(inode("boolean", _), 
                [
                    value
                ]
             ),
        m0
    ) = let
            val boolString = getLeaf(value)
            val v1Bool = valOf(Bool.fromString(boolString))
            val v1 = Boolean v1Bool
        in
            (v1, m0)
        end
  | typeOf(  itree(inode("ids", _), 
                [
                    id (*identifier*)
                ]
             ),
        m0
    ) = 
        let
          val varname = getLeaf(id)
          val loc0 = getLoc(accessEnv(varname, m0))
          val v = accessStore(loc0, m0)
          val label = getLabel(id)
        in
            (v, m0)
        end
           
 | typeOf(  itree(inode("ids", _),
                [
                    id (*identifier*),
                    itree(inode("++",_), [] )
                ]
             ),
        m0
    ) = let
            val varname = getLeaf(id)
            val loc0 = getLoc(accessEnv(varname, m0))
            val v = accessStore(loc0, m0)
            val vInt = getInt v
            val v0 = vInt+1 (*v + 1 need some more work*)
            val v1 = Integer v0
            val m1 = updateStore( (loc0, v1) , m0 )
        in
            (v, m1)
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
            val loc0 = getLoc(accessEnv(varname, m0))
            val v = accessStore(loc0, m0)
            val vInt = getInt v
            val v0 = vInt+1 (*v + 1 need some more work*)
            val v1 = Integer v0
            val m1 = updateStore( (loc0, v1) , m0 )
        in
            (v1, m1)
        end
        
 | typeOf(  itree(inode("ids", _), 
                [
                    id, (*identifier*)
                    itree(inode("--",_), [] )
                ]
             ),
        m0
    ) = let
            val varname = getLeaf(id)
            val loc0 = getLoc(accessEnv(varname, m0))
            val v = accessStore(loc0, m0)
            val vInt = getInt v
            val v0 = vInt-1 (*v - 1 need some more work*)
            val v1 = Integer v0
            val m1 = updateStore( (loc0, v1) , m0 )
        in
            (v, m1)
        end
 | typeOf(  itree(inode("ids", _),
                [
                    itree(inode("--",_), [] ),
                    id (*identifier*)
                ]
             ),
        m0
    ) = let
            val varname = getLeaf(id)
            val loc0 = getLoc(accessEnv(varname, m0))
            val v = accessStore(loc0, m0)
            val vInt = getInt v
            val v0 = vInt-1 (*v - 1 need some more work*)
            val v1 = Integer v0
            val m1 = updateStore( (loc0, v1) , m0 )
        in
            (v1, m1)
        end
  | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
  | E _ = raise Fail("error in typeCheck.typeOf - this should never occur")


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
		val t2 = getType(accessEnv(id,m))
	in
		if t1 = t2 then m else raise model_error
	end    
  | typeCheck( itree(inode("increment",_),
                [
                    increment
                ]
            ),
        m
    ) = typeCheck (increment, m)
  | typeCheck( itree(inode("block",_),
                [
                    itree(inode("{",_), [] ),
                    stmtList,                 
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
                    expr,                 
                    itree(inode("then",_), [] ),
                    block
                ]
            ),
        m0
    ) = let
		val t = typeOf(expr1)
		val m1=typeCheck(block1,m0)
	in
		if t = BOOL then m0 else raise model_error
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
		val t = typeOf(expr)
		val m1=typeCheck(block1,m0)
		val m2=typeCheck(block2,m0)
	in
		if t = BOOL then m0 else raise model_error
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
		val t = typeOf(expr)
		val m1=typeCheck(block,m0)
	in
		if t = BOOL then m0 else raise model_error
	end

  (*<forLoop> ::= "for" "(" <assign> ";" <expr> ";" <increment> ")" <block> .*)
  | typeCheck( itree(inode("forLoop",_),
                [
                    itree(inode("for",_), [] ),
                    itree(inode("(",_), [] ),
                    assign,
                    itree(inode(";",_), [] ),
                    expr,
                    itree(inode(";",_), [] ),
                    increment,
                    itree(inode(")",_), [] ),
                    block
                ]
            ),
        m
    ) = let
                val t=typeOf(expr)
                val m1=typeCheck(assign1,m)
                val m2=typeCheck(increment1,m)
                val m3=typeCheck(block1,m)
        in
                if t = BOOL then m else raise model_error
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
            val t = typeOf(expr,m)
        in
            if t != ERROR  then m0 else raise model_error			(!= means different here)
        end

  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)
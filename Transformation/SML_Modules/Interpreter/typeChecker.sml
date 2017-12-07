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
            val varname = getLeaf(id)
            val env1 = accessEnv (varname, m)
            val loc1 = getLoc env1
            val (v1, m1) = typeOf(expr0, m)
        in
            updateStore((loc1, v1 ), m1)
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
                typeCheck (increment, m)
            else 
                let
                    val (v, m1) = typeOf (increment, m)
                in
                    m1
                end
        end
  | typeCheck( itree(inode("block",_),
                [
                    itree(inode("{",_), [] ),
                    stmtList,                 
                    itree(inode("}",_), [] )
                ]
            ),
        m0 as (env0, loc0, s0)
    ) = let
            val (env1,loc1, s1) = typeCheck( stmtList, (env0, loc0, s0) )
            val m2 = (env0,loc0, s1)	
        in
                m2
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
            val (v1,m1) = typeOf( expr, m0 )
        in
            if (v1 = (Boolean true)) then typeCheck( block, m1) else m1
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
            val (v1,m1) = typeOf( expr, m0 )
        in
            if (v1 = (Boolean true)) then typeCheck( block1, m1) else typeCheck( block2, m1)
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
            fun N (expr1, block1, m0 ) =
                let
                      val (v,m1) = typeOf( expr1, m0 )
                in
                if (v = (Boolean true)) then
                      let
                              val m2 = typeCheck( block1, m1 )
                              val m3 = N( expr1, block1, m2 )
                      in
                              m3
                      end
                else m1
                end
        in
            N (expr, block, m0)
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
            fun P(assign1, expr1, increment1, block1, m0 ) =
                let
                    val m1 = typeCheck( assign1, m0 )
                    
                    fun Q(expr2, increment2, block2, m2 ) =
                    let
                          val (v,m3) = typeOf( expr2, m2 )
                    in
                        if (v = (Boolean true)) then
                               let
                                    val m4 = typeCheck( block2, m3 )
                                    val m5 = typeCheck( increment2, m4 )
                                    val m6 = Q( expr2, increment2, block2, m5 )
                               in
                                  m6
                               end
                        else m3
                    end
                in
                        Q(expr1, increment1, block1, m1 )
                end
        in
            P (assign, expr, increment, block, m)
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
            val (v1,m1) = typeOf( expr, m0 )
            val v1Int = getInt v1
            val v1String = Int.toString(v1Int)
        in
          (
            print("\n print = " ^ v1String);
            m1
          )
        end
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)
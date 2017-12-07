(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun getLabel (itree(inode(label,_), inf)) = label
  | getLabel _ = raise Fail("error - this should never occur")
  
fun getInt (Integer v) = v
    | getInt _ = raise Fail(" getInt : error - this should never occur")
    
fun getBool (Boolean v) = v
    | getBool _ = raise Fail(" getBool : error - this should never occur")
    
fun mypower ((m, n) :(int * int))
         = if n <= 0 
             then 1
           else (m * mypower(m, n-1)) :int

fun E(  itree(inode("expr", _), 
                [
                    disjunction
                ]
             ),
        m
    ) = E (disjunction, m)
  | E(  itree(inode("disjunction", _), 
                [
                    disjunction
                ]
             ),
        m
    ) = E (disjunction, m)
  | E(  itree(inode("conjunction", _),
                [
                    conjunction
                ]
             ),
        m
    ) = E (conjunction, m)
  | E(  itree(inode("equalitytest", _),
                [
                    equalitytest
                ]
             ),
        m
    ) = E (equalitytest, m)
  | E(  itree(inode("disjunction", _), 
                [
                    disjunction1,
                    itree(inode("||",_), [] ),
                    conjunction1
                ]
             ),
        m0
    ) = let 
            val (v1, m1) = E (disjunction1, m0)
        in
            if (v1 = (Boolean true)) then
                (v1, m1)
            else  	
                let 
                      val (v2, m2) = E(conjunction1, m1)
                in
                (v2, m2)
                end
        end
  | E(  itree(inode("conjunction", _), 
                [
                    conjunction1,
                    itree(inode("&&",_), [] ),
                    equalitytest1
                ]
             ),
        m0
    ) = let 
        val (v1, m1) = E (conjunction1, m0)
        in
            if (v1 = (Boolean true)) then
                let 
                        val (v2, m2) = E (equalitytest1, m1)
                in
                    (v2, m2)
                end
            else (v1, m1)
        end
        
  | E(  itree(inode("addsub", _),
                [
                    addsub
                ]
             ),
        m
    ) = E (addsub, m)
  | E(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("<",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let
            val (v1, m1) = E(equalitytest1, m0)
            val (v2, m2) = E(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int < v2Int) then Boolean true (*compare v1 < v2*)
                         else Boolean false
        in
                (result, m2)
        end
  | E(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode(">",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(equalitytest1, m0)
            val(v2, m2) = E(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int > v2Int) then Boolean true (*compare v1 > v2*)
                         else Boolean false
        in
                (result, m2)
        end
  | E(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("<=",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(equalitytest1, m0)
            val(v2, m2) = E(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int <= v2Int) then Boolean true (*compare v1 <= v2*)
                         else Boolean false
        in
                (result, m2)
        end
  | E(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode(">=",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(equalitytest1, m0)
            val(v2, m2) = E(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int >= v2Int) then Boolean true (*compare v1 >= v2*)
                         else Boolean false
        in
                (result, m2)
        end
  | E(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("==",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(equalitytest1, m0)
            val(v2, m2) = E(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int = v2Int) then Boolean true (*compare v1 == v2*)
                         else Boolean false
        in
                (result, m2)
        end
  | E(  itree(inode("equalitytest", _), 
                [
                    equalitytest1,
                    itree(inode("!=",_), [] ),
                    addsub1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(equalitytest1, m0)
            val(v2, m2) = E(addsub1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val result = if (v1Int <> v2Int) then Boolean true (*compare v1 != v2*)
                         else Boolean false
        in
                (result, m2)
        end
        
  | E(  itree(inode("multdivmod", _),
                [
                    multdivmod
                ]
             ),
        m
    ) = E (multdivmod, m)
  | E(  itree(inode("addsub", _), 
                [
                    addsub1,
                    itree(inode("+",_), [] ),
                    multdivmod1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(addsub1, m0)
            val(v2, m2) = E(multdivmod1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int + v2Int;
            val result = Integer v3Int (*compute v1 + v2*)
        in
                (result, m2)
        end
   
  | E(  itree(inode("addsub", _), 
                [
                    addsub1,
                    itree(inode("-",_), [] ),
                    multdivmod1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(addsub1, m0)
            val(v2, m2) = E(multdivmod1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int - v2Int;
            val result = Integer v3Int (*compute v1 - v2*)
        in
                (result, m2)
        end
        
  | E(  itree(inode("unaryminus", _),
                [
                    unaryminus
                ]
             ),
        m
    ) = E (unaryminus, m)
  | E(  itree(inode("multdivmod", _), 
                [
                    multdivmod1,
                    itree(inode("*",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(multdivmod1, m0)
            val(v2, m2) = E(unaryminus1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int * v2Int;
            val result = Integer v3Int (*compute v1 * v2*)
        in
                (result, m2)
        end
  | E(  itree(inode("multdivmod", _), 
                [
                    multdivmod1,
                    itree(inode("div",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(multdivmod1, m0)
            val(v2, m2) = E(unaryminus1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int div v2Int;
            val result = Integer v3Int (*compute v1 div v2*)
        in
                (result, m2)
        end
    | E(  itree(inode("multdivmod", _), 
                [
                    multdivmod1,
                    itree(inode("mod",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(multdivmod1, m0)
            val(v2, m2) = E(unaryminus1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = v1Int mod v2Int;
            val result = Integer v3Int (*compute v1 mod v2*)
        in
                (result, m2)
        end
        
  | E(  itree(inode("exponent", _),
                [
                    exponent
                ]
             ),
        m
    ) = E (exponent, m)
  | E(  itree(inode("unaryminus", _), 
                [
                    itree(inode("-",_), [] ),
                    unaryminus1
                ]
             ),
        m0
    ) = let
            val(v1, m1) = E(unaryminus1, m0)
            val v1Int = getInt v1;
            val v2Int = ~v1Int;
            val result = Integer v2Int (*compute ~v1*)
        in
                (result, m1)
        end
        
  | E(  itree(inode("notexpr", _),
                [
                    notexpr
                ]
             ),
        m0
    ) = E (notexpr, m0)
  | E(  itree(inode("exponent", _), 
                [
                    notexpr1,
                    itree(inode("^",_), [] ),
                    exponent1
                ]
             ),
        m0
    ) = let
            val (v1, m1) = E(notexpr1, m0)
            val (v2, m2) = E(exponent1, m1)
            val v1Int = getInt v1;
            val v2Int = getInt v2;
            val v3Int = mypower(v1Int, v2Int);
            val result = Integer v3Int (*compute v1 power v2*)
        in
                (result, m2)
        end
        
   | E(  itree(inode("factor", _),
                [
                    factor (*integer | boolean | <ids>*)
                ]
             ),
        m0
    ) = let
            val label = getLabel(factor)
        in
            E (factor, m0)
        end
    
  | E(  itree(inode("notexpr", _), 
                [
                    itree(inode("!",_), [] ),
                    notexpr1
                ]
             ),
        m0
    ) = let
            val (v1, m1) = E(notexpr1, m0)
            val v1Bool = getBool v1;
            val v2Bool = not(v1Bool);
            val result = Boolean v2Bool (*compute !v1*)
        in
                (result, m1)
        end
        
    | E(  itree(inode("factor", _), 
                [
                    itree(inode("(",_), [] ),
                    expr1,
                    itree(inode(")",_), [] )
                ]
             ),
        m0
    ) = let
            val (v1, m1) = E(expr1, m0)
        in
                (v1, m1)
        end
    | E(  itree(inode("factor", _), 
                [
                    itree(inode("|",_), [] ),
                    expr1,
                    itree(inode("|",_), [] )
                ]
             ),
        m0
    ) = let
            val (v1, m1) = E(expr1, m0)
            val v1Int = getInt v1;
            val v2Int = if (v1Int > 0) then v1Int else ~v1Int 
            val result = Integer v2Int
        in
                (result, m1)
        end
  (*| E(  itree(inode("factor", _), 
                [
                    expr1 (*integer | boolean | <ids>*)
                ]
             ),
        m0
    ) = E(expr1, m0) removed for now because duplicate*)
    
  | E(  itree(inode("integer", _), 
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
  | E(  itree(inode("boolean", _), 
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
  | E(  itree(inode("ids", _), 
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
           
 | E(  itree(inode("ids", _),
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
 | E(  itree(inode("ids", _), 
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
        
 | E(  itree(inode("ids", _), 
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
 | E(  itree(inode("ids", _),
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


 | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
 | E _ = raise Fail("error in Semantics.E - this should never occur")

(*
  prog ::= stmtList
  M([[stmtList1]] , m) = M(stmtList1, m)
*)
fun M(  itree(inode("prog",_), 
                [ 
                    stmtList
                ] 
             ),
        m
    ) = M(stmtList, m)
  | M( itree(inode("stmtList",_),
                [
                    stmt,
                    itree(inode(";",_), [] ),
                    stmtList
                ]
            ),
        m       
    ) = M( stmtList, M(stmt, m))
  | M( itree(inode("stmtList",_),
                [
                    epsilon
                ]
            ),
        m       
    ) = m
  | M( itree(inode("stmt",_),
                [
                    anyStmt
                ]
            ),
        m       
    ) = M(anyStmt, m)
  | M( itree(inode("dec",_),
                [
                    itree(inode("int",_), [] ),                 
                    id
                ]
            ),
        m      
    ) = updateEnv( getLeaf(id), INT, m )
  | M( itree(inode("dec",_),
                [
                    itree(inode("bool",_), [] ),                 
                    id
                ]
            ),
        m     
    ) = updateEnv( getLeaf(id), BOOL, m )
    | M( itree(inode("assign",_),
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
            val (v1, m1) = E(expr0, m)
        in
            updateStore((loc1, v1 ), m1)
        end     
  | M( itree(inode("increment",_),
                [
                    increment
                ]
            ),
        m
    ) = let
            val label = getLabel(increment)
        in
            if (label = "assign") then
                M (increment, m)
            else 
                let
                    val (v, m1) = E (increment, m)
                in
                    m1
                end
        end
  | M( itree(inode("block",_),
                [
                    itree(inode("{",_), [] ),
                    stmtList,                 
                    itree(inode("}",_), [] )
                ]
            ),
        m0 as (env0, loc0, s0)
    ) = let
            val (env1,loc1, s1) = M( stmtList, (env0, loc0, s0) )
            val m2 = (env0,loc0, s1)	
        in
                m2
        end
  | M( itree(inode("conditional",_),
                [
                    itree(inode("if",_), [] ),
                    expr,                 
                    itree(inode("then",_), [] ),
                    block
                ]
            ),
        m0
    ) = let
            val (v1,m1) = E( expr, m0 )
        in
            if (v1 = (Boolean true)) then M( block, m1) else m1
        end
  | M( itree(inode("conditional",_),
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
            val (v1,m1) = E( expr, m0 )
        in
            if (v1 = (Boolean true)) then M( block1, m1) else M( block2, m1)
        end
  | M( itree(inode("whileLoop",_),
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
                      val (v,m1) = E( expr1, m0 )
                in
                if (v = (Boolean true)) then
                      let
                              val m2 = M( block1, m1 )
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
  | M( itree(inode("forLoop",_),
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
                    val m1 = M( assign1, m0 )
                    
                    fun Q(expr2, increment2, block2, m2 ) =
                    let
                          val (v,m3) = E( expr2, m2 )
                    in
                        if (v = (Boolean true)) then
                               let
                                    val m4 = M( block2, m3 )
                                    val m5 = M( increment2, m4 )
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
  | M( itree(inode("printStmt",_),
                [
                    itree(inode("print",_), [] ),
                    itree(inode("(",_), [] ),
                    expr,                 
                    itree(inode(")",_), [] )
                ]
            ),
        m0
    ) = let
            val (v1,m1) = E( expr, m0 )
            val v1Int = getInt v1
            val v1String = Int.toString(v1Int)
        in
          (
            print("\n print = " ^ v1String);
            m1
          )
        end
  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)
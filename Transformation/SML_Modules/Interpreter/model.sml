(* =========================================================================================================== *)
exception runtime_error;
fun error msg = ( print msg; raise runtime_error );
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;

fun typeToString INT = "INT"
| typeToString BOOL = "BOOL"
| typeToString ERROR = "ERROR";

(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;

fun getTypeOfVal (Boolean _) = "BOOL"
| getTypeOfVal (Integer _) = "INT";

type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:loc, []:store )

(* =========================================================================================================== *)

(********** Update Env **********)
fun updateEnv( id, t, (e, count, s) ) = 
 ((id, t, count)::e, count+1, s);

(********** Access Env **********)
fun accessEnv(id,([], lo, s)) = error "Error: Illegal env access"
| accessEnv(id,((id1,t1,loc1)::es, lo, s)) = 
    if id = id1 then (id1, t1, loc1) else accessEnv (id, (es, lo, s));

(********** Get Location **********)
fun getLoc (id, t, lo) = lo;

(********** Get Type **********)
fun getType (id, t, lo) = t;

(********** Update Store - beginning **********)
fun update(tuple, []) = [tuple]
| update(tuple2 as (loc2, v2), (tuple1 as (loc1, v1))::s) = 
if loc2 = loc1 then tuple2::s
else tuple1::update(tuple2, s);

fun updateStore (tuple, (e:env, l:loc, s:store)) = 
let
    val (location, value) = tuple 
    val temp = update(tuple, s)
in
    (e, l, temp)
end;
(********** Update Store - end **********)

fun stringDv(Boolean dv)=Bool.toString(dv)
| stringDv(Integer dv)=Int.toString(dv)

fun printEnv([])=() 
| printEnv((id1,t1:types,loc1:loc)::env)=
(

    print(id1 ^ "\t" ^ typeToString(t1) ^ "\t" ^  Int.toString(loc1) ^ "\n");
    printEnv(env)
);

fun printStore([])=()
| printStore((loc2:loc,v1:denotable_value)::store)=
(
    
    print(Int.toString(loc2) ^ "\t" ^ stringDv(v1) ^ "\n");
    printStore(store)
);

fun printModel([],addressCounter,[])=() 
| printModel(env,addressCounter, store)=
(
    print("Address Counter:\t"^Int.toString(addressCounter)^"\n");
    print("ENV\n");
    print("==============\n");
    printEnv(env);
    print("==============\n");
    print("Store\n");
    print("==============\n");
    printStore(store);
    print("==============\n")

);

(********** Access Store **********)
fun accessStore(lo,(e, lo1, [])) = error "Error: Illegal store access"
| accessStore(lo,(e, lo1, (loc1, v1)::s)) = 
    if lo = loc1 then v1 else accessStore (lo, (e, lo1, s));    

end; (* struct *) 
(* =========================================================================================================== *)
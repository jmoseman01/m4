(* =========================================================================================================== *)
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


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;


type loc   = int
type env   = (string * types * loc) list
type store = (loc * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, []:store )


fun typeToString(t1:types)=if t1=INT then "INT"
else if t1=BOOL then "BOOL"
else ""

fun stringDv(Boolean dv)=Bool.toString(dv)
| stringDv(Integer dv)=Int.toString(dv)

fun printModel(_,[])=() 
| printModel([],_)=() 
| printModel((envr as (id1,t1:types,loc1:loc))::env,(storer as (loc2:loc,v1:denotable_value))::store)=
(
    print("ENV\n");
    print("==============\n");
    print(id1 ^ "\t" ^ typeToString(t1) ^ "\t" ^  Int.toString(loc1) ^ "\n");
    print("==============\n");
    print("Store\n");
    print("==============\n");
    print(Int.toString(loc2) ^ "\t" ^ stringDv(v1) ^ "\n");
    print("==============\n")
);
(* =========================================================================================================== *)

(********** Update Env **********)
fun updateEnv( id,t,loc, (env,s) ) = 
      (
      print ("\n id = " ^ id);
        ((id,t,loc)::env,s)
      );

(********** Access Env **********)
fun accessEnv(id,([], s)) = ("error", INT, 1)
| accessEnv(id,((id1,t1,loc1)::es, s)) = 
    if id = id1 then (id1, t1, loc1) else accessEnv (id, (es, s));

(********** Get Location **********)
fun getLoc (id, t, loc) = loc;

(********** Update Store **********)
fun update(tuple, []) = [tuple]
| update(tuple2 as (loc2, v2), (tuple1 as (loc1, v1))::s) = 
if loc2 = loc1 then tuple2::s
else tuple1::update(tuple2, s);

fun updateStore (tuple, (e:env, s:store)) = 
let
    val temp = update(tuple, s)
in
    (e,temp)
end;

(********** Access Store **********)
fun accessStore(loc,(env, [])) = Integer 1
| accessStore(loc,(env, (loc1, v1)::s)) = 
    if loc = loc1 then v1 else accessStore (loc, (env, s));
    
(*fun printModel ([],_) = (print ("\n"))
| printModel ((varname,type0,location)::env, (storetuple as (type1,value))::store) = 
        (
        print ("\n " ^ varname);
        print ("\n " ^ Int.toString(type1));
        printModel(env,storetuple::store)
        )
    ;*)
    

end; (* struct *) 
(* =========================================================================================================== *)













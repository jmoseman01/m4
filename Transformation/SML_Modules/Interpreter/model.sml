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
val initialModel = ( []:env, 0:loc, []:store )

fun updateEnv(id, t:types, loc:loc, (env:env,l:loc,s:store)) = 
          ((id,t,loc)::env,l,s)

fun dvToString(Integer x)=Int.toString(x)
| dvToString(Boolean x)=Bool.toString(x);

fun printModel(env,next,s)=
let
    val x=print("Next"^Int.toString(next)^"\n")
    
    fun aux1 [] = []
        | aux1((loc,dv)::ss)=
        let
            val _ = print ("LOc:"^(Int.toString(loc))^"Value"^(dvToString(dv))^"\n")
        
        in
            aux1(ss)
        end
    in
        aux1(s)
    end;

fun getLoc(id,t,loc)=loc;

fun getId(id,t,loc)=id;

fun error msg = ( print msg; raise runtime_error);

fun accessEnv(idinp,m as (([],loc,store:store)))=error "can't access identifier"
| accessEnv(idinp,m as ((envr as (id,t,eloc))::env,loc,store:store))=if idinp=id then envr else accessEnv(idinp,m);

fun accessStore(locinp:loc,m as (env:env,l:loc,[]:store))=error "can't accesss store by loc"
| accessStore(locinp:loc,m as (env:env,l:loc,(sv as (sloc,svalue))::store:store))=if sloc=locinp then sv else accessStore(locinp,m);

fun updateStore(loc,value,(env:env,l:loc,store:store))=
              (env,l,(loc,value)::store)
              
fun printIdInEnv(m)=(print( (getId(accessEnv("x",m)))^"\n"));

(*accessEnv,accessStore,updateEnv,updateStore,getLoc,getType,showEnv*)
(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)
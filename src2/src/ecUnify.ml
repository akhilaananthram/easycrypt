(* -------------------------------------------------------------------- *)
open EcMaps
open EcUtils
open EcUidgen
open EcTypes

(* -------------------------------------------------------------------- *)
exception TypeVarCycle of uid * ty
exception UnificationFailure of ty * ty

type unienv = (ty EcUidgen.Muid.t) ref

module UniEnv = struct
  let create () =
    ref (EcUidgen.Muid.empty : ty EcUidgen.Muid.t)

  let copy (ue : unienv) =
    ref !ue

  let restore ~(dst:unienv) ~(src:unienv) =
    dst := !src

  let asmap (ue : unienv) =
    !ue

  let dump pp (ue : unienv) =
    let pp_binding pp (a, ty) =
      EcDebug.onhlist pp (string_of_int a)
        (EcTypes.ty_dump) [ty]
    in
      EcDebug.onhseq
        pp "Unification Environment" pp_binding
        (EcUidgen.Muid.to_stream !ue)

  let repr (ue : unienv) (t : ty) : ty = 
    match t with
    | Tunivar id -> odfl t (Muid.find_opt id !ue)
    | _ -> t

  let bind (ue : unienv) id t =
    match t with
    | Tunivar id' when uid_equal id id' -> ()
    | _ -> begin
      if (Muid.mem id !ue) || (occur_uni id t) then
        raise (TypeVarCycle (id, t));
      ue :=
        Muid.add id (EcTypes.Subst.uni !ue t)
        (Muid.map (EcTypes.Subst.uni1 (id, t)) !ue)
    end
end

(* -------------------------------------------------------------------- *)
let unify (env : EcEnv.env) (ue : unienv) =
  let rec unify (t1 : ty) (t2 : ty) = 
    match UniEnv.repr ue t1, UniEnv.repr ue t2 with
    | Tvar i1, Tvar i2 -> 
        (* FIXME use equal *)
        if not (EcIdent.id_equal i1 i2) then 
          raise (UnificationFailure (t1, t2))

    | Tunivar id, t | t, Tunivar id -> UniEnv.bind ue id t

    | Ttuple lt1, Ttuple lt2 ->
        if List.length lt1 <> List.length lt2 then 
          raise (UnificationFailure (t1, t2));
        List.iter2 unify lt1 lt2

    | Tconstr(p1, lt1), Tconstr(p2, lt2) when EcPath.p_equal p1 p2 ->
        if List.length lt1 <> List.length lt2 then
          raise (UnificationFailure (t1, t2));
        List.iter2 unify lt1 lt2

    | Tconstr(p, lt), t when EcEnv.Ty.defined p env ->
        unify (EcEnv.Ty.unfold p lt env) t

    | t, Tconstr(p, lt) when EcEnv.Ty.defined p env ->
        unify t (EcEnv.Ty.unfold p lt env)

    | _, _ -> raise (UnificationFailure(t1, t2))

  in
    unify

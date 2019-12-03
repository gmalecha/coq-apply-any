let do_hint hnt = assert false

let rec each = function
  | [] -> Tacticals.New.tclFAIL 0 Pp.(str "no applicable hint")
  | h :: hs ->
     Proofview.tclOR (do_hint h) (fun _ -> each hs)

let the_tactic use_e db_name =
  try
    let db = Hints.searchtable_map db_name in
    Proofview.Goal.enter begin fun gl ->
      let c = Proofview.Goal.concl gl in
      let s = Proofview.Goal.sigma gl in
      let sv = Auto.compute_secvars gl in
      let hints =
        try
          if EConstr.isApp s c then
            let f,xs = EConstr.decompose_app s c in
            let gr = Globnames.global_of_constr (EConstr.to_constr ~abort_on_undefined_evars:true s f) in
            Hints.Hint_db.map_eauto s ~secvars:sv (gr, Array.of_list xs) c db
          else
            let gr = Globnames.global_of_constr (EConstr.to_constr ~abort_on_undefined_evars:true s c) in
            Hints.Hint_db.map_eauto s ~secvars:sv (gr, Array.of_list []) c db
        with _ -> []
      in
      each hints
      end
  with Not_found ->
    Proofview.Goal.enter (fun _ ->
        Tacticals.New.tclFAIL 0 Pp.(str "Hint database " ++ str db_name ++ str " not found!"))

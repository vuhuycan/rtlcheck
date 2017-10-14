Require Import Arith.
Require Import List.
Require Import String.
Require Import Ascii.
Require Import PipeGraph.Debug.
Require Import PipeGraph.Util.
Require Import PipeGraph.StringUtil.
Require Import PipeGraph.Instruction.
Require Import PipeGraph.Graph.
Require Import PipeGraph.FOLPredicate.
Require Import PipeGraph.GraphvizCompressed.
Require Import PipeGraph.ConstraintTreeTypes.

Open Scope string_scope.

Import ListNotations.

Definition ToString
  (n : nat)
  : string :=
  stringOfNat n.

Definition GetBaseIndex
  (c : nat)
  : nat :=
  match c with
  | 0 => 1
  | 1 => 6
  | 2 => 11
  | 3 => 16
  | _ => Warning 1 ["Trying to get base mem index of an undefined core!"]
  end.


Definition GetPCofMicroop
  (uop : Microop)
  (bases : list (nat * nat))
  : string :=
  let c := coreID uop in
  let t := match (find (fun x => beq_nat c (fst x)) bases) with
           | None => Warning 0 ["Could not find base PC for core "; ToString c]
           | Some (c', b) => (globalID uop) - b
           end
  in
  ToString (((GetBaseIndex c) * 4) + (t * 4)).


(* We don't technically need to pass along the core for these functions, but it makes things easier. *)
Definition MapFetch
  (uop : Microop)
  (core : nat)
  (bases : list (nat * nat))
  : list string :=
  ["core_gen_block["; ToString core; "].vscale.pipeline.PC_IF == 32'd"; GetPCofMicroop uop bases;
    " && ~(core_gen_block["; ToString core; "].vscale.pipeline.stall_IF || core_gen_block["; ToString core; "].vscale.pipeline.kill_IF)"].

Definition MapDecEx
  (uop : Microop)
  (core : nat)
  (bases : list (nat * nat))
  : list string :=
  ["core_gen_block["; ToString core; "].vscale.pipeline.PC_DX == 32'd"; GetPCofMicroop uop bases; " && ~(core_gen_block["; ToString core; "].vscale.pipeline.stall_DX)"].

Definition MapWB
  (uop : Microop)
  (core : nat)
  (bases : list (nat * nat))
  (lc: list ScenarioTree)
  : list string :=
  let base_prop :=
      ["core_gen_block["; ToString core; "].vscale.pipeline.PC_WB == 32'd"; GetPCofMicroop uop bases; " && ~(core_gen_block[";
      ToString core; "].vscale.pipeline.stall_WB)"] in
  let f x := match x with
             | ScenarioLoadConstraint op _ _ => beq_uop op uop
             | _ => false
             end in
  match find f lc with
  | Some x => match x with
              | ScenarioLoadConstraint op dat neg =>
                    let eq_str := if neg then "!=" else "==" in
                    match dat with
                    | NormalData n =>
                        app base_prop [" && core_gen_block["; ToString core; "].vscale.pipeline.load_data_WB "; eq_str; " 32'd"; ToString n]
                    | _ => Warning base_prop ["Something other than NormalData here!"]
                    end
              | _ => Warning base_prop ["Should have gotten a ScenarioLoadConstraint but got something else!"]
              end
  | None => base_prop
  end.

(* Node mapping function for Vscale. *)
Definition MapNodeVscale
  (n : GraphNode)
  (bases : list (nat * nat))
  (lc: list ScenarioTree)
  : list string :=
  let (uop, loc) := n in
  let (_, stage) := loc in
  let core := coreID uop in
  match stage with
  (* Fetch *)
  | 0 => MapFetch uop core bases
  (* DecodeExecute *)
  | 1 => MapDecEx uop core bases
  (* Writeback *)
  | 2 => MapWB uop core bases lc
  | _ => Warning [] ["Trying to map undefined stage!"]
  end.

Definition GetMemIndexForAddr
  (for_reg : bool)
  (n : nat)
  : nat :=
  if for_reg then (84 + (n * 4)) else (21 + n).

Fixpoint GetAddresses
  (l : list Microop)
  (addrs : list PhysicalAddress)
  : list PhysicalAddress :=
  let get_addr x :=
        match x with
        | Read _ _ a _ => Some a
        | Write _ _ a _ => Some a
        | _ => None
        end
  in
  match l with
  | [] => addrs
  | h::t => match (get_addr (access h)) with
            | None => GetAddresses t addrs
            | Some a => if (find (beq_paddr a) addrs) then GetAddresses t addrs else GetAddresses t (a::addrs)
            end
  end.

Fixpoint GetInitialConditionMapping
  (conditions : list BoundaryCondition)
  (pa : PhysicalAddress)
  : Data :=
  match conditions with
  | (a, d) :: t =>
      if beq_paddr a pa
      then d
      else GetInitialConditionMapping t pa
  | [] =>
      let result := NormalData 0 in
      if PrintFlag 6
      then Comment result
        ["Using implicit initial condition data=0 for PA: ";
        GraphvizStringOfPhysicalAddress pa]
      else result
  end.

Definition FindInitialState
  (init: list BoundaryCondition)
  (addr : PhysicalAddress)
  : (PhysicalAddress * Data) :=
  (addr, (GetInitialConditionMapping init addr)).

Fixpoint AddToThread
  (uop : Microop)
  (l : list (nat * (list Microop)))
  : list (nat * (list Microop)) :=
  match l with
  | [] => [((coreID uop), [uop])]
  | h::t => if (beq_nat (coreID uop) (fst h)) then ((fst h), (app (snd h) [uop]))::t else h::(AddToThread uop t)
  end.

Fixpoint FilterUops
  (l : list Microop)
  (l' : list (nat * (list Microop)))
  : list (nat * (list Microop)) :=
  match l with
  | [] => l'
  | h::t => FilterUops t (AddToThread h l')
  end.

(* For halt logic. *)
Fixpoint AddCoreUopList
  (n : nat)
  (l : list (nat * (list Microop)))
  : list (nat * (list Microop)) :=
  match l with
  | [] => [(n, [])]
  | h::t => if beq_nat (fst h) n then l else h::(AddCoreUopList n t)
  end.

Fixpoint EnsureCores
  (max_core_id : nat)
  (l : list (nat * (list Microop)))
  : list (nat * (list Microop)) :=
  match max_core_id with
  | 0 => AddCoreUopList max_core_id l
  | S n' => EnsureCores n' (AddCoreUopList max_core_id l)
  end.

Fixpoint FindAddressReg
  (base : nat)
  (addrs : list (nat * nat))
  (tag : nat)
  : (nat * (nat * (list (nat * nat)))) :=
  match addrs with
  | [] => (base, ((S base), ((tag, base)::addrs)))
  | h::t => if beq_nat tag (fst h) then ((snd h), (base, addrs)) else FindAddressReg base t tag
  end.

Fixpoint GetMemIndexOf
  (uop : Microop)
  (bases : list (nat * nat))
  : nat :=
  let c := coreID uop in
  let t := match (find (fun x => beq_nat c (fst x)) bases) with
           | None => Warning 0 ["Could not find base mem index for core "; ToString c]
           | Some (c', b) => (globalID uop) - b
           end
  in
  (GetBaseIndex c) + t.

Fixpoint MapInitMemInstrsHelper
  (assume_outer : string)
  (bases : list (nat * nat))
  (thread : list Microop)
  (base : nat) (* the reg to use next *)
  (l : list (nat * nat)) (* which registers have been used for which address *)
  (assums : list string)
  (regs : list (nat * nat)) (* reg * value *)
  (cur_index : nat) (* the index to use for the halt instruction *)
  : (list (nat * nat) * (list string)) := (* core * reg * value *)
  let f d :=
      match d with
      | NormalData n => n
      | _ => Warning 0 ["Found something other than NormalData!"]
      end
  in
  let g d :=
      match d with
      | PTag n => n
      | _ => Warning 0 ["Found something other than PTag!"]
      end
  in
  match thread with
  | [] => let assums := app assums [assume_outer; "hasti_mem.mem["; ToString cur_index;
                                    "] == `RV32_HALT);"; newline] in
        (regs, assums)
  | h::t =>
        match access h with
        | Write _ _ a d =>
              let (tag, index) := a in
              let tag := g tag in
              let (cur, bl) := FindAddressReg base l tag in (* For the address reg *)
              let (base', l') := bl in
              MapInitMemInstrsHelper assume_outer bases t (S base') l' (app assums [assume_outer; "hasti_mem.mem["; ToString (GetMemIndexOf h bases);
               "] == {7'b0,5'd"; ToString base'; ",5'd"; ToString cur; ",3'd2,5'b0,`RV32_STORE});"; newline])
               (app ((cur, GetMemIndexForAddr true tag)::regs) [(base', f d)]) (* This trickery is deliberate. I want the data assumptions to be at the end. *)
               (S (GetMemIndexOf h bases))
        | Read _ _ a d =>
              let (tag, index) := a in
              let tag := g tag in
              let (cur, bl) := FindAddressReg base l tag in (* For the address reg *)
              let (base', l') := bl in
              MapInitMemInstrsHelper assume_outer bases t (S base') l' (app assums [assume_outer; "hasti_mem.mem["; ToString (GetMemIndexOf h bases);
               "] == {12'b0,5'd"; ToString cur; ",3'd2,5'd"; ToString base'; ",`RV32_LOAD});"; newline]) ((cur, GetMemIndexForAddr true tag)::regs) (S (GetMemIndexOf h bases))
        | Fence _ =>
              MapInitMemInstrsHelper assume_outer bases t base l (app assums [assume_outer; "hasti_mem.mem["; ToString (GetMemIndexOf h bases);
               "] == {4'b0,8'b1,5'b0,3'b`RV32_FUNCT3_FENCE,5'b0,`RV32_MISC_MEM});"; newline]) regs (S (GetMemIndexOf h bases))
        | _ => Warning ([], []) ["Mapping an instr other than a load/store/fence!"]
        end
  end.

Fixpoint AddCoreID
  (n : nat)
  (l : list (nat * nat))
  : list (nat * (nat * nat)) :=
  match l with
  | [] => []
  | h::t => (n, h)::(AddCoreID n t)
  end.

Definition MapInitMemInstrs
  (assume_outer : string)
  (bases : list (nat * nat))
  (threads : nat * (list Microop))
  : (list (nat * (nat * nat)) * (list string)) := (* core * reg * value *)
  let t := (MapInitMemInstrsHelper assume_outer bases (snd threads) 1 [] [] [] (GetBaseIndex (fst threads))) in
  ((AddCoreID (fst threads) (fst t)), (snd t)).

Definition GetAssumptionsFromTuples
  (l1 : list string)
  (l2 : list (nat * (nat * nat)) * (list string))
  : list string :=
  app l1 (snd l2).

Definition GetRegsFromTuples
  (l1 : list (nat * (nat * nat)))
  (l2 : list (nat * (nat * nat)) * (list string))
  : list (nat * (nat * nat)) :=
  app l1 (fst l2).

Definition TranslateAddrInits
  (assume_outer : string)
  (tup: PhysicalAddress * Data)
  : list string :=
  let f d :=
      match d with
      | NormalData n => n
      | _ => Warning 0 ["Found something other than NormalData!"]
      end
  in
  let g d :=
      match d with
      | PTag n => n
      | _ => Warning 0 ["Found something other than PTag!"]
      end
  in
  [assume_outer; "hasti_mem.mem["; ToString (GetMemIndexForAddr false (g (ptag (fst tup)))); "] == {32'd"; ToString (f (snd tup)); "});"; newline].

Definition TranslateInitReg
  (assume_outer : string)
  (tup : nat * (nat * nat)) (* core * reg * data *)
  : list string :=
  [assume_outer; "core_gen_block["; ToString (fst tup);
  "].vscale.pipeline.regfile.data["; ToString (fst (snd tup)); "] == 32'd"; ToString (snd (snd tup)); ");"; newline].

Definition MapAssumptions
  (assume_outer : string)
  (bases : list (nat * nat))
  (inits : list (PhysicalAddress * Data))
  (threads : list (nat * (list Microop)))
  : list string :=
  let im := Map (MapInitMemInstrs assume_outer bases) threads in
  let instr_mem_assums := fold_left GetAssumptionsFromTuples im [] in
  let data_mem_assums := fold_left (fun x y => app x y) (Map (TranslateAddrInits assume_outer) (rev inits)) [] in
  let used_regs := fold_left GetRegsFromTuples im [] in
  let regs_assums := fold_left (fun x y => app x y) (Map (TranslateInitReg assume_outer) used_regs) [] in
  app (app instr_mem_assums data_mem_assums) regs_assums.

Definition AddShadowState
  (l : list string)
  : list string :=
  let l' := ["reg run_once_clk;"; newline; newline;
             "always @(posedge clk) begin"; newline;
             tab; "if (reset) begin"; newline;
                tab; tab; "run_once_clk <= 0;"; newline;
                   tab; "end else if (run_once_clk == 0) begin"; newline;
                       tab; tab; "run_once_clk <= 1;"; newline;
                         tab; "end"; newline;
                            "end"; newline; newline] in

  app l' l.

Fixpoint PrintLoadValueAssumptionsHelper
  (assume_outer : string)
  (bases : list (nat * nat))
  (l : list Microop)
  (l' : list string)
  : list string :=
  let f x := match x with
             | [] => true
             | _ => false
             end in
  match l with
  | [] => app (assume_outer::l') ["));"; newline]
  | h::t => let str_add := if f t then ["))"] else [")) and "; newline] in 
            match access h with
            | Read _ _ a d =>
                PrintLoadValueAssumptionsHelper assume_outer bases t (app l' (app (app ("(("::(MapWB h (coreID h) bases [])) (") |-> ("::(MapWB h (coreID h) bases [ScenarioLoadConstraint h d false]))) str_add))
            | _ => PrintLoadValueAssumptionsHelper assume_outer bases t l'
            end
  end.

Definition PrintLoadValueAssumptions
  (assume_outer : string)
  (bases : list (nat * nat))
  (l : list Microop)
  (l' : list string)
  : list string :=
  match l with
  | [] => []
  | _ => PrintLoadValueAssumptionsHelper assume_outer bases l l'
  end.

Definition GenFinalStatePrecond
  (core : nat)
  : list string :=
  ["(core_gen_block["; ToString core; "].vscale.pipeline.halted == 1'b1 && core_gen_block["; ToString core; "].vscale.pipeline.PC_WB == 32'd120 && ~(core_gen_block[";
  ToString core; "].vscale.pipeline.stall_WB))"].

Definition AddAnd
  (l : list string)
  (l' : list string)
  : list string :=
  match l with
  | [] => l'
  | _ => app l (" && "::l')
  end.

Definition MapFinalStatePrecond
  (rtl_map_fn : string)
  (cores : list nat)
  : list string :=
  let str_cmp := beq_string rtl_map_fn "Vscale_TSO" in
  match str_cmp with
  | true => app ("("::(fold_left AddAnd (Map GenFinalStatePrecond cores) [])) [")"]
  | _ => app ("("::(fold_left AddAnd (Map GenFinalStatePrecond cores) [])) [")"]
  end.

Definition MapFinalStateHelper
  (b : BoundaryCondition)
  : list string :=
  let f d :=
      match d with
      | NormalData n => n
      | _ => Warning 0 ["Found something other than NormalData!"]
      end
  in
  let g d :=
      match d with
      | PTag n => n
      | _ => Warning 0 ["Found something other than PTag!"]
      end
  in
  ["hasti_mem.mem["; ToString (GetMemIndexForAddr false (g (ptag (fst b)))); "] == {32'd"; ToString (f (snd b)); "}"].

Fixpoint MapFinalState
  (l : list BoundaryCondition)
  (l' : list string)
  : list string :=
  match l with
  | [] => l'
  | h::t => match l' with
            | [] => MapFinalState t (app ("("::(MapFinalStateHelper h)) [")"])
            | _  => MapFinalState t (app l' (" && "::(app ("("::(MapFinalStateHelper h)) [")"])))
            end
  end.


Definition PrintFinalValueAssumptions
  (rtl_map_fn : string)
  (assume_outer : string)
  (l : list BoundaryCondition)
  (l' : list string)
  : list string :=
  (* We need to have the assumption be true in the case where there are NO final state conditions, hence the "1" in the call to MapFinalState. *)
  let str_cmp := beq_string rtl_map_fn "Vscale_TSO" in
  match str_cmp with
  | true => app (app (assume_outer::(MapFinalStatePrecond rtl_map_fn [0; 1; 2; 3])) (" |-> ("::(MapFinalState l ["1"]))) [")));"]
  | _ => app (app (assume_outer::(MapFinalStatePrecond rtl_map_fn [0; 1; 2; 3])) (" |-> ("::(MapFinalState l ["1"]))) [")));"]
  end.

(* The program mapping function for Vscale. *)
Definition PrintRTLAssumptionsVscale
  (bases : list (nat * nat))
  (l : list Microop)
  (unch_loads : list Microop)
  (initial : list BoundaryCondition)
  (final : list BoundaryCondition)
  (rtl_map_fn : string)
  : list string :=
  let addrs := GetAddresses l [] in
  let addr_inits := Map (FindInitialState initial) addrs in
  let threads := FilterUops l [] in
  let pad_threads := EnsureCores 3 threads in (* cores are zero-indexed... *)
  let assume_outer := "assume property (@(posedge clk) ~run_once_clk |-> " in
  let assume_outer' := "assume property (@(posedge clk) (" in
  let f x := match access x with
             | Read _ _ _ _ => true
             | _ => false
             end in
  app (app (app (AddShadowState (MapAssumptions assume_outer bases addr_inits pad_threads)) (PrintLoadValueAssumptions assume_outer' bases (filter f unch_loads) []))
    (PrintFinalValueAssumptions rtl_map_fn assume_outer' final [])) [newline].


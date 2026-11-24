import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split at the only negation into two monotone gate lists.
-- Pinning the negated signal separately at false and at true forces
-- witnesses among the edges and the maximal independent sets.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2046_1
    (witnesses : let E : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
      let N : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
      ∀ P S : Circuit, Monotone2 P → Monotone2 S → P.size + S.size = 13 →
      let W := fun (r : ℕ) => P.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 && r.testBit 2])
      let H := fun (r : ℕ) (b : Bool) => S.eval (W r ++ [b])
      let U := fun (r : ℕ) => (W r).getD P.output false
      (∀ r ∈ E, H r (!U r) = true) → (∀ r ∈ N, H r (!U r) = false) →
      (∃ r ∈ E, H r false = false) ∧ ∃ r ∈ N, H r true = true)
    (remaining : let E : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
      let N : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
      ∀ P S : Circuit, Monotone2 P → Monotone2 S → P.size + S.size = 13 →
      let W := fun (r : ℕ) => P.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 && r.testBit 2])
      let H := fun (r : ℕ) (b : Bool) => S.eval (W r ++ [b])
      let U := fun (r : ℕ) => (W r).getD P.output false
      (∃ p ∈ E, ∃ n ∈ N, U p = false ∧ U n = true ∧ H p false = false ∧ H n true = true) →
      ∃ r : Fin 512, H r.val (!U r.val) ≠ E.any (fun e => (r.val &&& e) == e)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) := by
  let E : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
  let N : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
  let xrow := fun (r : ℕ) (i : Fin 9) => r.testBit i.val
  let F : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have pos (r : ℕ) (hr : r ∈ E) : F (xrow r) = true := by
    simp only [E, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have negRow (r : ℕ) (hr : r ∈ N) : F (xrow r) = false := by
    simp only [N, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have table : ∀ r : Fin 512, F (xrow r.val) = E.any (fun e => (r.val &&& e) == e) := by
    decide +kernel
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have prefixOK (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      obtain ⟨t, ht, size⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [size]⟩
      rw [List.foldl_cons, ht]
      simp [step]
  let test := fun (g : Gate) => GateOp.rec (motive := fun _ => Bool)
    false false true (fun _ => false) false g.op
  have isNot (g : Gate) : test g = true ↔ g.op = GateOp.not := by
    obtain ⟨op,ins⟩ := g
    cases op <;> simp [test]
  intro C legal first size count correct
  obtain ⟨gs,o⟩ := C
  rcases gs with _ | ⟨g0, gs⟩
  · change 0 = 15 at size
    contradiction
  · have firstVal (x : Fin 9 → Bool) :
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 && x 2) := by
      let b := g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)
      have h := first x
      change (gs.foldl step (List.ofFn x ++ [b])).getD 9 false = _ at h
      obtain ⟨t, ht, _⟩ := prefixOK gs (List.ofFn x ++ [b])
      rw [ht, List.getD_append _ _ _ _ (by simp)] at h
      change b = _
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp :
        (List.ofFn x).length ≤ 9), List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero,
        Option.getD_some] using h
    have firstPositive : test g0 = false := by
      by_contra! bad
      have nop := (isNot g0).mp (Bool.eq_true_of_not_eq_false bad)
      let empty := fun _ : Fin 9 => false
      have zeros (i : ℕ) : (List.ofFn empty).getD i false = false := by
        by_cases hi : i < 9
        · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
          exact List.getElem_ofFn (by simpa using hi)
        · exact List.getD_eq_default _ _ (by simp; omega)
      have h := firstVal empty
      rw [nop] at h
      change (!(g0.inputs.map (fun i => (List.ofFn empty).getD i false)).headD false) = false at h
      cases l : g0.inputs with
      | nil => simp [l] at h
      | cons i tail => simp only [l, List.map_cons, List.headD_cons, zeros, Bool.not_false] at h; contradiction
    change (g0 :: gs).countP test = 1 at count
    rw [List.countP_cons] at count
    have cnt : gs.countP test = 1 := by simpa only [firstPositive, Bool.false_eq_true, if_false, Nat.add_zero] using count
    obtain ⟨notGate, hg, flag⟩ := List.countP_pos_iff.mp (show 0 < gs.countP test by omega)
    have nOp := (isNot notGate).mp flag
    obtain ⟨pre, post, perm⟩ := List.append_of_mem hg
    have counts : pre.countP test = 0 ∧ post.countP test = 0 := by
      rw [perm, List.countP_append, List.countP_cons] at cnt
      simp only [flag, if_true] at cnt
      omega
    let P : Circuit := ⟨pre, notGate.inputs.headD (10 + pre.length)⟩
    let S : Circuit := ⟨post, o⟩
    have mono (ls : List Gate) (out : ℕ) (sub : ∀ g ∈ ls, g ∈ gs) (zero : ls.countP test = 0) :
        Monotone2 ⟨ls,out⟩ := by
      intro g h
      obtain ⟨basis, length⟩ := legal g (List.mem_cons_of_mem _ (sub g h))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at basis ⊢
      have notN : g.op ≠ GateOp.not := fun eq => List.countP_eq_zero.mp zero g h ((isNot g).mpr eq)
      exact ⟨basis.elim Or.inl (fun b => Or.inr (b.resolve_right notN)), length⟩
    have mp : Monotone2 P := mono pre _ (fun g h => by simp [perm, h]) counts.1
    have ms : Monotone2 S := mono post _ (fun g h => by simp [perm, h]) counts.2
    have total : P.size + S.size = 13 := by
      change pre.length + post.length = _
      have h : (g0 :: gs).length = 15 := size
      simp [perm, Nat.add_assoc] at h
      omega
    let W := fun (r : ℕ) => P.wires (List.ofFn (xrow r) ++ [(xrow r) 0 && (xrow r) 2])
    let H := fun (r : ℕ) (b : Bool) => S.eval (W r ++ [b])
    let U := fun (r : ℕ) => (W r).getD P.output false
    have actual (r : ℕ) : H r (!U r) = F (xrow r) := by
      let x := xrow r
      let raw := List.ofFn x ++ [x 0 && x 2]
      have init : step (List.ofFn x) g0 = raw := by simp only [step, raw, firstVal]
      have wdef : W r = pre.foldl step raw := rfl
      have len : (W r).length = 10 + pre.length := by
        obtain ⟨t, ht, sizeT⟩ := prefixOK pre raw
        rw [wdef, ht]
        simp only [raw, List.length_append, List.length_ofFn, List.length_singleton, sizeT] <;> omega
      have bit : notGate.op.eval (notGate.inputs.map fun k => (W r).getD k false) = !U r := by
        rw [nOp]
        change (!(notGate.inputs.map fun k => (W r).getD k false).headD false) =
          !((W r).getD (notGate.inputs.headD (10 + pre.length)) false)
        cases ls : notGate.inputs with
        | nil => simp [← len, List.getD_eq_getElem?_getD]
        | cons k rest => rfl
      have eq := congrFun correct x
      change ((g0 :: gs).foldl step (List.ofFn x)).getD o false = F x at eq
      rw [List.foldl_cons, init, perm, List.foldl_append, List.foldl_cons, ← wdef] at eq
      change S.eval (W r ++ [notGate.op.eval (notGate.inputs.map fun k => (W r).getD k false)]) = F x at eq
      rw [bit] at eq
      exact eq
    obtain ⟨⟨p,pe,hp⟩,n,nn,hn⟩ := witnesses P S mp ms total
      (fun r hr => (actual r).trans (pos r hr)) (fun r hr => (actual r).trans (negRow r hr))
    change H p false = false at hp
    change H n true = true at hn
    have up : U p = false := by
      cases eq : U p with
      | false => rfl
      | true =>
        have impossible := (actual p).trans (pos p pe)
        rw [eq, Bool.not_true, hp] at impossible
        contradiction
    have un : U n = true := by
      cases eq : U n with
      | true => rfl
      | false =>
        have impossible := (actual n).trans (negRow n nn)
        rw [eq, Bool.not_false, hn] at impossible
        contradiction
    obtain ⟨r,miss⟩ := remaining P S mp ms total ⟨p,pe,n,nn,up,un,hp,hn⟩
    exact miss ((actual r.val).trans (table r))

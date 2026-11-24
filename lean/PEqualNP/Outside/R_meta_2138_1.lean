import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- At input six equal to false, a second gate reading the first conjunction
-- supplies a constant or an existing input. The exception is a NOT whose
-- second, ignored operand is the conjunction and whose first is a raw input.
theorem PEqualNP.Outside.R_meta_2138_1
    (compress : ∀ (T : Circuit) (h : (Fin 9 → Bool) → Bool), FanInTwo T →
      ((∃ i : Fin 9, h = fun x => x i) ∨ (∃ b : Bool, h = fun _ => b)) →
      let f := fun x : Fin 9 → Bool => T.eval (List.ofFn x ++ [false, h x])
      f (fun i => decide (i = 8)) ≠ f (fun i => decide (i = 6 ∨ i = 8)) →
      f (fun _ => false) ≠ f (fun i => decide (i = 1 ∨ i = 2)) →
      ∃ D : Circuit, FanInTwo D ∧ (D.size = 0 ∨ D.size + 1 ≤ T.size) ∧
        ∀ y : Fin 9 → Bool, y 6 = false →
          circuitFun 8 D (fun j => y ((6 : Fin 9).succAbove j)) = f y)
    (minor : ∀ D : Circuit, FanInTwo D → circuitFun 8 D = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 7 && x 5)) → 13 ≤ D.size)
    (exceptional : ∀ (i : Fin 9) (T : Circuit), FanInTwo T →
      (∀ x : Fin 9 → Bool, T.eval (List.ofFn x ++ [x 0 && x 6, !x i]) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x) → 14 ≤ T.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∃ x2 ∈ x1.gates[(1 : ℕ)]?.toList, (9 : ℕ) ∈ x2.inputs) → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  let graph : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let small : (Fin 8 → Bool) → Bool := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 6) || (x 7 && x 5)
  let wire := fun (x : Fin 9 → Bool) (b : Bool) (k : ℕ) => (List.ofFn x ++ [b]).getD k false
  let gate := fun (g : Gate) (x : Fin 9 → Bool) (b : Bool) => g.op.eval (g.inputs.map (wire x b))
  let simple := fun h : (Fin 9 → Bool) → Bool =>
    (∃ i : Fin 9, h = fun x => x i) ∨ (∃ b : Bool, h = fun _ => b)
  have raw (x : Fin 9 → Bool) (b : Bool) (k : ℕ) (hk : k < 9) : wire x b k = x ⟨k,hk⟩ := by
    dsimp only [wire]
    rw [List.getD_append _ _ _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk)]
    exact List.getElem_ofFn (by simpa only [List.length_ofFn] using hk)
  have ninth (x : Fin 9 → Bool) (b : Bool) : wire x b 9 = b := by
    simp [wire, List.getD_eq_getElem?_getD]
  have absent (x : Fin 9 → Bool) (b : Bool) (k : ℕ) (hk : 10 ≤ k) : wire x b k = false :=
    List.getD_eq_default _ _ (by simp; omega)
  have ws (k : ℕ) : simple (fun x => wire x false k) := by
    by_cases hk : k < 9
    · exact Or.inl ⟨⟨k,hk⟩, funext (fun x => raw x false k hk)⟩
    · refine Or.inr ⟨false, funext (fun x => ?_)⟩
      by_cases eq : k = 9
      · exact eq ▸ ninth x false
      · exact absent x false k (by omega)
  have evalAnd (bits : List Bool) : GateOp.and.eval bits = bits.all id := rfl
  have evalOr (bits : List Bool) : GateOp.or.eval bits = bits.any id := rfl
  have evalNot (bits : List Bool) : GateOp.not.eval bits = !(bits.headD false) := rfl
  have classify (g : Gate) (basis : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
      (len : g.inputs.length ≤ 2) (mem : 9 ∈ g.inputs) :
      simple (fun x => gate g x false) ∨ ∃ i : Fin 9, ∀ x b, gate g x b = !x i := by
    have shape : g.inputs = [9] ∨ (∃ k, g.inputs = [9,k]) ∨ ∃ k, g.inputs = [k,9] := by
      cases e : g.inputs with
      | nil => simp [e] at mem
      | cons a tail =>
        cases tail with
        | nil => simpa [e] using (show 9 = a by simpa [e] using mem).symm
        | cons b rest =>
          cases rest with
          | nil =>
            have ab : 9 = a ∨ 9 = b := by simpa [e] using mem
            rcases ab with h | h
            · exact Or.inr (Or.inl ⟨b, by simp [h]⟩)
            · exact Or.inr (Or.inr ⟨a, by simp [h]⟩)
          | cons c l => simp [e] at len
    rcases basis with hand | hor | hnot
    · left
      right
      refine ⟨false, funext (fun x => ?_)⟩
      rcases shape with hs | ⟨k, hs⟩ | ⟨k, hs⟩ <;> simp [gate, hs, hand, evalAnd, ninth]
    · left
      rcases shape with hs | ⟨k, hs⟩ | ⟨k, hs⟩
      · exact Or.inr ⟨false, by funext x; simp [gate, hs, hor, evalOr, ninth]⟩
      · simpa [gate, hs, hor, evalOr, ninth] using ws k
      · simpa [gate, hs, hor, evalOr, ninth] using ws k
    · rcases shape with hs | ⟨k, hs⟩ | ⟨k, hs⟩
      · exact Or.inl (Or.inr ⟨true, by funext x; simp [gate, hs, hnot, evalNot, ninth]⟩)
      · exact Or.inl (Or.inr ⟨true, by funext x; simp [gate, hs, hnot, evalNot, ninth]⟩)
      · by_cases hk : k < 9
        · exact Or.inr ⟨⟨k,hk⟩, fun x b => by simp [gate, hs, hnot, evalNot, raw x b k hk]⟩
        · refine Or.inl (Or.inr ⟨true, funext (fun x => ?_)⟩)
          by_cases eq : k = 9
          · simp [gate, hs, hnot, evalNot, eq, ninth]
          · simp [gate, hs, hnot, evalNot, absent x false k (by omega)]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have prefixOkay (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp⟩
    | cons g gs ih =>
      obtain ⟨t, ht⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
      rw [List.foldl_cons, ht]
      simp [step]
  intro C reads good first computes
  obtain ⟨gs, o⟩ := C
  rcases gs with _ | ⟨g0, _ | ⟨g1, tail⟩⟩
  · simp at reads
  · simp at reads
  · let T : Circuit := ⟨tail, o⟩
    have okT : FanInTwo T := fun g hg => good g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
    have sizeEq : (Circuit.mk (g0 :: g1 :: tail) o).size = T.size + 2 := rfl
    have run (x : Fin 9 → Bool) :
        T.eval (List.ofFn x ++ [x 0 && x 6, gate g1 x (x 0 && x 6)]) = graph x := by
      let w := List.ofFn x
      let b := g0.op.eval (g0.inputs.map fun i => w.getD i false)
      have fb := first x
      change ((g1 :: tail).foldl step (w ++ [b])).getD 9 false = _ at fb
      obtain ⟨t, ht⟩ := prefixOkay (g1 :: tail) (w ++ [b])
      rw [ht, List.getD_append _ _ _ _ (by simp [w])] at fb
      have eq : b = (x 0 && x 6) := (ninth x b).symm.trans fb
      have full := congrFun computes x
      change T.eval ((w ++ [b]) ++ [gate g1 x b]) = graph x at full
      simpa only [eq, List.append_assoc, List.singleton_append] using full
    have read9 : 9 ∈ g1.inputs := by simpa using reads
    have good1 := good g1 (List.mem_cons_of_mem g0 List.mem_cons_self)
    rcases classify g1 good1.1 good1.2 read9 with sh | ⟨i, neg⟩
    · let f := fun x : Fin 9 → Bool => T.eval (List.ofFn x ++ [false, gate g1 x false])
      let put := fun (b : Bool) (x : Fin 8 → Bool) => Fin.insertNth (α := fun _ : Fin 9 => Bool) (6 : Fin 9) b x
      have slice (x : Fin 9 → Bool) (hz : (x 0 && x 6) = false) : f x = graph x := by
        simpa only [hz] using run x
      have dep : f (fun i => decide (i = 8)) ≠ f (fun i => decide (i = 6 ∨ i = 8)) := by
        rw [slice _ (by decide), slice _ (by decide)]
        decide
      have nc : f (fun _ => false) ≠ f (fun i => decide (i = 1 ∨ i = 2)) := by
        rw [slice _ (by decide), slice _ (by decide)]
        decide
      obtain ⟨D, okD, saved, preserves⟩ := compress T (fun x => gate g1 x false) okT sh dep nc
      have smallEq : circuitFun 8 D = small := by
        funext x
        let y := put false x
        have at6 : y 6 = false := Fin.insertNth_apply_same _ _ _
        have at0 : y 0 = x 0 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (0 : Fin 8)
        have at1 : y 1 = x 1 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (1 : Fin 8)
        have at2 : y 2 = x 2 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (2 : Fin 8)
        have at3 : y 3 = x 3 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (3 : Fin 8)
        have at4 : y 4 = x 4 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (4 : Fin 8)
        have at5 : y 5 = x 5 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (5 : Fin 8)
        have at7 : y 7 = x 6 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (6 : Fin 8)
        have at8 : y 8 = x 7 := Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false x (7 : Fin 8)
        have hy := preserves y at6
        have back : (fun j : Fin 8 => y ((6 : Fin 9).succAbove j)) = x :=
          funext (fun j => Fin.insertNth_apply_succAbove (α := fun _ => Bool) 6 false x j)
        rw [back] at hy
        change circuitFun 8 D x = f y at hy
        rw [hy, slice y (by simp [at6])]
        simp only [graph, small, at0, at1, at2, at3, at4, at5, at6, at7, at8, Bool.and_false,
          Bool.false_and, Bool.or_false, Bool.false_or]
      have bound := minor D okD smallEq
      omega
    · have bound := exceptional i T okT (fun x => by simpa only [neg] using run x)
      omega

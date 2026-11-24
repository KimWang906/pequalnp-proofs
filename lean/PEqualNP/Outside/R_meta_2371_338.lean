import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- At least fifteen gates combine signals, so at most three signals need
-- a stored complement. A vertex permutation moves every complemented raw
-- input into one of four triples while preserving the Petersen function.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2371_338
    (binary : ∀ (C : Circuit) (b : Bool), FanInTwo C →
      (∀ x : Fin 10 → Bool, (if b then !(circuitFun 10 C x) else circuitFun 10 C x) = (fun x : Fin 10 → Bool => (List.finRange 5).any (fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)))) x) →
      15 ≤ C.gates.countP (fun g => g.op.eval [true,true]))
    (compile : ∀ (α : Type) (X : List (α → Bool)) (C : Circuit), FanInTwo C →
      let A := (fun _ => false) :: (fun _ => true) :: X
      ∃ G M : List (α → Bool), G.length = C.gates.countP (fun g => g.op.eval [true,true]) ∧
        G.length + M.length ≤ C.size ∧ (∀ i : Fin G.length, let W := A ++ G.take i.val
        let allow := fun f => f ∈ W ∨ ∃ u ∈ W, u ∈ M ∧ f = fun x => !u x
        ∃ a b, allow a ∧ allow b ∧
          ((G.get i = fun x => a x && b x) ∨ G.get i = fun x => a x || b x)) ∧
        ∃ v ∈ A ++ G,
          (∀ x, C.eval (X.map fun f => f x) = v x) ∨
          (∀ x, C.eval (X.map fun f => f x) = !v x))
    (symmetries : let F := fun x : Fin 10 → Bool => (List.finRange 5).any (fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)))
      ∀ s : List (Fin 10), s.length ≤ 3 → ∃ p : Equiv.Perm (Fin 10),
        (∀ x : Fin 10 → Bool, F (x ∘ p) = F x) ∧ ∃ m ∈ ([7,11,42,50] : List ℕ),
          ∀ i ∈ s, m.testBit (p i).val = true)
    (search : let F := fun x : Fin 10 → Bool => (List.finRange 5).any (fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)))
      let A : List ((Fin 10 → Bool) → Bool) := (fun _ => false) :: (fun _ => true) :: (List.ofFn fun i : Fin 10 => fun x : Fin 10 → Bool => x i)
      ∀ G M : List ((Fin 10 → Bool) → Bool), 15 ≤ G.length → G.length + M.length ≤ 18 →
        (∃ m ∈ ([7,11,42,50] : List ℕ), ∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ M →
          m.testBit i.val = true) →
        (∀ i : Fin G.length, let W := A ++ G.take i.val
        let allow := fun f => f ∈ W ∨ ∃ u ∈ W, u ∈ M ∧ f = fun x => !u x
        ∃ a b, allow a ∧ allow b ∧
          ((G.get i = fun x => a x && b x) ∨ G.get i = fun x => a x || b x)) → ∀ v ∈ A ++ G, ∀ b : Bool, ∃ x : Fin 10 → Bool,
        (if b then !v x else v x) ≠ F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10 := by
  classical
  let F := fun x : Fin 10 → Bool => (List.finRange 5).any (fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i+1))) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i+2))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)))
  let raw := fun (i : Fin 10) (x : Fin 10 → Bool) => x i
  let X := List.ofFn raw
  let A : List ((Fin 10 → Bool) → Bool) := (fun _ => false) :: (fun _ => true) :: X
  have rawMem (i : Fin 10) : raw i ∈ A := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have input (x : Fin 10 → Bool) : X.map (fun f => f x) = List.ofFn x := by simp only [X, List.map_ofFn]; rfl
  intro gate tail out b legalHead legalTail budget target run
  by_contra! allRows
  let C : Circuit := ⟨gate :: tail.gates, out⟩
  have ok : FanInTwo C := by
    intro g hg
    rcases List.mem_cons.mp hg with h | h
    · exact h ▸ legalHead gate List.mem_cons_self
    · exact legalTail g h
  have total : C.size ≤ 18 := by change tail.size + 1 ≤ 18; omega
  have formula : ∀ x : Fin 10 → Bool, target x = F x := by decide +kernel
  have actual (x : Fin 10 → Bool) : (if b then !(circuitFun 10 C x) else circuitFun 10 C x) = F x :=
    (allRows x).trans (formula x)
  obtain ⟨G,M,count,spent,legal,v,hv,hvEval⟩ := compile (Fin 10 → Bool) X C ok
  change v ∈ A ++ G at hv
  have lower := binary C b ok actual
  have gl : 15 ≤ G.length := by omega
  have ml : M.length ≤ 3 := by omega
  let idx (f : (Fin 10 → Bool) → Bool) : Fin 10 :=
    if h : ∃ i, f = raw i then h.choose else 0
  have rawInject : Function.Injective raw := by
    intro i j e
    have h := congrFun e (fun k : Fin 10 => decide (k = i))
    have ji : j = i := by simpa [raw] using h.symm
    exact ji.symm
  have idxRaw (i : Fin 10) : idx (raw i) = i := by
    have ex : ∃ j, raw i = raw j := ⟨i,rfl⟩
    change (if h : ∃ j, raw i = raw j then h.choose else 0) = i
    rw [dif_pos ex]
    exact (rawInject ex.choose_spec).symm
  obtain ⟨p, symmF, m, mask, cover⟩ := symmetries (M.map idx) (by simpa using ml)
  change (∀ x : Fin 10 → Bool, F (x ∘ p) = F x) at symmF
  let ρ (f : (Fin 10 → Bool) → Bool) := fun x : Fin 10 → Bool => f (x ∘ p)
  have stays (f : (Fin 10 → Bool) → Bool) (hf : f ∈ A) : ρ f ∈ A := by
    rcases List.mem_cons.mp hf with h | h
    · subst f; exact List.mem_cons_self
    · rcases List.mem_cons.mp h with h | h
      · subst f; exact List.mem_cons_of_mem _ List.mem_cons_self
      · obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
        rw [← hi]
        exact rawMem (p i)
  have includePool (L : List ((Fin 10 → Bool) → Bool)) (f : (Fin 10 → Bool) → Bool) (hf : f ∈ A ++ L) : ρ f ∈ A ++ L.map ρ := by
    rcases List.mem_append.mp hf with h | h
    · exact List.mem_append_left _ (stays f h)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have aligned (i : Fin 10) (h : raw i ∈ M.map ρ) : m.testBit i.val = true := by
    obtain ⟨u, hu, e⟩ := List.mem_map.mp h
    have orig : u = raw (p.symm i) := by
      funext x
      have hh := congrFun e (x ∘ p.symm)
      change u ((x ∘ p.symm) ∘ p) = x (p.symm i) at hh
      have inv : (x ∘ p.symm) ∘ p = x := by funext j; simp
      rwa [inv] at hh
    have hv := cover (idx u) (List.mem_map.mpr ⟨u,hu,rfl⟩)
    rwa [orig, idxRaw, Equiv.apply_symm_apply] at hv
  have admissible := search (G.map ρ) (M.map ρ) (by simpa using gl) (by simpa using (show G.length + M.length ≤ 18 by omega))
    ⟨m,mask,aligned⟩ (by
      intro k
      let j : Fin G.length := ⟨k.val, by simpa using k.isLt⟩
      obtain ⟨a,c,ha,hc,kind⟩ := legal j
      have transport (f : (Fin 10 → Bool) → Bool)
          (h : f ∈ A ++ G.take k.val ∨ ∃ u ∈ A ++ G.take k.val, u ∈ M ∧ f = fun x => !u x) :
          ρ f ∈ A ++ (G.map ρ).take k.val ∨ ∃ u ∈ A ++ (G.map ρ).take k.val,
            u ∈ M.map ρ ∧ ρ f = fun x => !u x := by
        rw [← List.map_take]
        rcases h with pos | ⟨u,hu,hm,e⟩
        · exact Or.inl (includePool _ f pos)
        · exact Or.inr ⟨ρ u, includePool _ u hu, List.mem_map.mpr ⟨u,hm,rfl⟩, congrArg ρ e⟩
      refine ⟨ρ a, ρ c, transport a ha, transport c hc, ?_⟩
      have atK : (G.map ρ).get k = ρ (G.get j) := by simp [List.get_eq_getElem, j]
      rw [atK]
      exact kind.elim (fun e => Or.inl (congrArg ρ e)) (fun e => Or.inr (congrArg ρ e)))
    (ρ v) (includePool G v hv)
  rcases hvEval with direct | flipped
  · obtain ⟨x, hx⟩ := admissible b
    have e := direct (x ∘ p)
    rw [input] at e
    have a := actual (x ∘ p)
    change (if b then !(C.eval (List.ofFn (x ∘ p))) else C.eval (List.ofFn (x ∘ p))) = F (x ∘ p) at a
    rw [e, symmF x] at a
    exact hx a
  · obtain ⟨x, hx⟩ := admissible (!b)
    have e := flipped (x ∘ p)
    rw [input] at e
    have a := actual (x ∘ p)
    change (if b then !(C.eval (List.ofFn (x ∘ p))) else C.eval (List.ofFn (x ∘ p))) = F (x ∘ p) at a
    rw [e, symmF x] at a
    apply hx
    cases b <;> simpa only [ρ, Bool.not_true, Bool.not_false, Bool.not_not, if_true, Bool.false_eq_true, if_false] using a

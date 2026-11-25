import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12408

open PEqualNP.CircuitLowerBounds

def target : Fin 4 → Finset (Fin 14)
  | ⟨0, _⟩ => {0, 2, 4, 6, 8, 10, 12}
  | ⟨1, _⟩ => {1, 2, 5, 6, 9, 10, 13}
  | ⟨2, _⟩ => {3, 4, 5, 6, 11, 12, 13}
  | ⟨3, _⟩ => {7, 8, 9, 10, 11, 12, 13}

def W0 : Finset (Finset (Fin 14)) :=
  Finset.univ.image (fun p : Fin 14 => ({p} : Finset (Fin 14)))

def gateSupp (W : List (Finset (Fin 14))) (g : Gate) : Finset (Fin 14) :=
  (g.inputs.map (fun i => W.getD i ∅)).foldr (· ∪ ·) ∅

def stepSupp (W : List (Finset (Fin 14))) (g : Gate) : List (Finset (Fin 14)) :=
  W ++ [gateSupp W g]

def initSupps : List (Finset (Fin 14)) :=
  List.ofFn (fun p : Fin 14 => ({p} : Finset (Fin 14)))

def allSupps (gs : List Gate) : List (Finset (Fin 14)) :=
  gs.foldl stepSupp initSupps

lemma any_map_decide_mem (l : List (Finset (Fin 14))) (p : Fin 14) :
    (l.map (fun s => decide (p ∈ s))).any id = decide (p ∈ l.foldr (· ∪ ·) ∅) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, id_eq, List.foldr_cons, Finset.mem_union, ih]
    by_cases h1 : p ∈ a <;> by_cases h2 : p ∈ t.foldr (· ∪ ·) ∅ <;> simp [h1, h2]

lemma getD_map_decide (W : List (Finset (Fin 14))) (p : Fin 14) (i : ℕ) :
    (W.map (fun s => decide (p ∈ s))).getD i false = decide (p ∈ W.getD i ∅) := by
  by_cases hi : i < W.length
  · simp [List.getD, hi]
  · simp [List.getD, hi]

lemma wires_eq_map_allSupps (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.or)
    (W : List (Finset (Fin 14))) (p : Fin 14) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map (fun s => decide (p ∈ s))) =
    (gs.foldl stepSupp W).map (fun s => decide (p ∈ s)) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g rest ih =>
    have hg : g.op = GateOp.or := hgs g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ rest, g'.op = GateOp.or := fun g' hg' =>
      hgs g' (List.mem_cons_of_mem _ hg')
    simp only [List.foldl_cons, stepSupp]
    have hstep :
        W.map (fun s => decide (p ∈ s)) ++
          [g.op.eval (g.inputs.map fun i => (W.map (fun s => decide (p ∈ s))).getD i false)] =
        (W ++ [gateSupp W g]).map (fun s => decide (p ∈ s)) := by
      rw [hg, List.map_append, List.map_singleton]
      congr 1
      simp only [GateOp.eval, gateSupp]
      have hmap : (g.inputs.map fun i => (W.map (fun s => decide (p ∈ s))).getD i false) =
          (g.inputs.map fun i => W.getD i ∅).map (fun s => decide (p ∈ s)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact getD_map_decide W p i
      rw [hmap, any_map_decide_mem]
      rfl
    rw [hstep]
    exact ih hrest (W ++ [gateSupp W g])

lemma initSupps_map_decide (p : Fin 14) :
    initSupps.map (fun s => decide (p ∈ s)) = List.ofFn (fun q : Fin 14 => decide (q = p)) := by
  simp only [initSupps, List.map_ofFn]
  congr 1
  funext q
  simp [eq_comm]

lemma wires_getD_eq_decide (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or) (w : ℕ) (p : Fin 14) :
    (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
    decide (p ∈ (allSupps C.gates).getD w ∅) := by
  unfold Circuit.wires allSupps
  rw [← initSupps_map_decide p, wires_eq_map_allSupps C.gates hC initSupps p, getD_map_decide]

lemma target_0 : target 0 = {(0 : Fin 14), 2, 4, 6, 8, 10, 12} := rfl
lemma target_1 : target 1 = {(1 : Fin 14), 2, 5, 6, 9, 10, 13} := rfl
lemma target_2 : target 2 = {(3 : Fin 14), 4, 5, 6, 11, 12, 13} := rfl
lemma target_3 : target 3 = {(7 : Fin 14), 8, 9, 10, 11, 12, 13} := rfl

lemma mem_target_iff (v : Fin 4) (p : Fin 14) :
    p ∈ target v ↔ Nat.testBit (p.val + 1) v.val = true := by
  rcases v with ⟨v, hv⟩
  rcases p with ⟨n, hn⟩
  rw [Nat.testBit_eq_decide_div_mod_eq]
  match v, hv with
  | 0, _ =>
    simp only [target, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, decide_eq_true_eq]
    omega
  | 1, _ =>
    simp only [target, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, decide_eq_true_eq]
    omega
  | 2, _ =>
    simp only [target, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, decide_eq_true_eq]
    omega
  | 3, _ =>
    simp only [target, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, decide_eq_true_eq]
    omega

lemma target_nonempty (v : Fin 4) : (target v).Nonempty := by
  rcases v with ⟨v, hv⟩
  match v, hv with
  | 0, _ => exact ⟨0, by simp [target]⟩
  | 1, _ => exact ⟨1, by simp [target]⟩
  | 2, _ => exact ⟨3, by simp [target]⟩
  | 3, _ => exact ⟨7, by simp [target]⟩

lemma target_mem_allSupps (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or)
    (hcomp : ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14,
      (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
      Nat.testBit (p.val + 1) v.val)
    (v : Fin 4) :
    target v ∈ (allSupps C.gates).toFinset := by
  obtain ⟨w, hw⟩ := hcomp v
  have hEq : (allSupps C.gates).getD w ∅ = target v := by
    ext p
    have hp := hw p
    rw [wires_getD_eq_decide C hC w p] at hp
    rw [mem_target_iff, ← hp, decide_eq_true_eq]
  have hwlt : w < (allSupps C.gates).length := by
    by_contra hge
    have hemp : (allSupps C.gates).getD w ∅ = ∅ := by simp [List.getD, hge]
    rw [hemp] at hEq
    exact (target_nonempty v).ne_empty hEq.symm
  rw [List.mem_toFinset, ← hEq, List.getD_eq_getElem _ _ hwlt]
  exact List.getElem_mem hwlt

lemma W0_subset_initSupps : W0 ⊆ initSupps.toFinset := by
  intro s hs
  simp only [W0, Finset.mem_image, Finset.mem_univ, true_and] at hs
  obtain ⟨p, rfl⟩ := hs
  rw [List.mem_toFinset, initSupps, List.mem_ofFn]
  exact ⟨p, rfl⟩

lemma foldl_stepSupp_subset (gs : List Gate) (W : List (Finset (Fin 14))) :
    W.toFinset ⊆ (gs.foldl stepSupp W).toFinset := by
  induction gs generalizing W with
  | nil => exact Finset.Subset.rfl
  | cons g rest ih =>
    intro s hs
    apply ih (stepSupp W g)
    simp only [stepSupp, List.toFinset_append, Finset.mem_union]
    exact Or.inl hs

lemma gateSupp_eq_union (W : List (Finset (Fin 14))) (g : Gate) (hg : g.inputs.length ≤ 2) :
    ∃ A B : Finset (Fin 14),
      (A = ∅ ∨ A ∈ W.toFinset) ∧ (B = ∅ ∨ B ∈ W.toFinset) ∧ gateSupp W g = A ∪ B := by
  have hget : ∀ i : ℕ, W.getD i ∅ = ∅ ∨ W.getD i ∅ ∈ W.toFinset := by
    intro i
    by_cases hi : i < W.length
    · right
      rw [List.mem_toFinset, List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · left
      simp [List.getD, hi]
  rcases g with ⟨op, inps⟩
  match inps with
  | [] =>
    exact ⟨∅, ∅, Or.inl rfl, Or.inl rfl, by simp [gateSupp]⟩
  | [i] =>
    exact ⟨W.getD i ∅, ∅, hget i, Or.inl rfl, by simp [gateSupp]⟩
  | [i, j] =>
    exact ⟨W.getD i ∅, W.getD j ∅, hget i, hget j, by simp [gateSupp]⟩
  | _ :: _ :: _ :: _ =>
    simp at hg

def isCover (v : Fin 4) (W C : Finset (Finset (Fin 14))) : Prop :=
  C ⊆ W ∧ C.biUnion id = target v

lemma exists_cover_of_W0_subset (v : Fin 4) (W : Finset (Finset (Fin 14))) (hW : W0 ⊆ W) :
    ∃ k : ℕ, ∃ C : Finset (Finset (Fin 14)), isCover v W C ∧ C.card = k := by
  refine ⟨((target v).image (fun p => ({p} : Finset (Fin 14)))).card,
    (target v).image (fun p => ({p} : Finset (Fin 14))), ⟨?_, ?_⟩, rfl⟩
  · intro s hs
    apply hW
    simp only [Finset.mem_image] at hs
    obtain ⟨p, _, rfl⟩ := hs
    simp [W0]
  · ext p
    simp

noncomputable def coverNum (v : Fin 4) (W : Finset (Finset (Fin 14))) : ℕ :=
  open Classical in
  if h : ∃ k : ℕ, ∃ C : Finset (Finset (Fin 14)), isCover v W C ∧ C.card = k then
    Nat.find h
  else 0

lemma coverNum_le (v : Fin 4) (W C : Finset (Finset (Fin 14))) (hC : isCover v W C) :
    coverNum v W ≤ C.card := by
  classical
  have hex : ∃ k : ℕ, ∃ C' : Finset (Finset (Fin 14)), isCover v W C' ∧ C'.card = k :=
    ⟨C.card, C, hC, rfl⟩
  unfold coverNum
  rw [dif_pos hex]
  exact Nat.find_min' hex ⟨C, hC, rfl⟩

lemma exists_min_cover (v : Fin 4) (W : Finset (Finset (Fin 14))) (hW : W0 ⊆ W) :
    ∃ C : Finset (Finset (Fin 14)), isCover v W C ∧ C.card = coverNum v W := by
  classical
  have hex := exists_cover_of_W0_subset v W hW
  unfold coverNum
  rw [dif_pos hex]
  exact Nat.find_spec hex

lemma coverNum_pos (v : Fin 4) (W : Finset (Finset (Fin 14))) (hW : W0 ⊆ W) :
    1 ≤ coverNum v W := by
  obtain ⟨C, ⟨_, hU⟩, hcard⟩ := exists_min_cover v W hW
  rw [← hcard]
  have hne : C.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.biUnion_empty] at hU
    exact (target_nonempty v).ne_empty hU.symm
  exact Finset.one_le_card.mpr hne

lemma coverNum_eq_one (v : Fin 4) (W : Finset (Finset (Fin 14)))
    (hW : W0 ⊆ W) (ht : target v ∈ W) :
    coverNum v W = 1 := by
  apply le_antisymm
  · have hle := coverNum_le v W {target v} ⟨Finset.singleton_subset_iff.mpr ht, by simp⟩
    simpa using hle
  · exact coverNum_pos v W hW

lemma coverNum_mono (v : Fin 4) (W1 W2 : Finset (Finset (Fin 14)))
    (hW1 : W0 ⊆ W1) (hsub : W1 ⊆ W2) :
    coverNum v W2 ≤ coverNum v W1 := by
  obtain ⟨C, ⟨hCW, hU⟩, hcard⟩ := exists_min_cover v W1 hW1
  rw [← hcard]
  exact coverNum_le v W2 C ⟨hCW.trans hsub, hU⟩

lemma coverNum_insert_of_not_subset (v : Fin 4) (W : Finset (Finset (Fin 14)))
    (hW : W0 ⊆ W) (X : Finset (Fin 14)) (hX : ¬ X ⊆ target v) :
    coverNum v (insert X W) = coverNum v W := by
  apply le_antisymm
  · exact coverNum_mono v W (insert X W) hW (Finset.subset_insert X W)
  · obtain ⟨C, ⟨hCW, hU⟩, hcard⟩ := exists_min_cover v (insert X W) (hW.trans (Finset.subset_insert X W))
    rw [← hcard]
    apply coverNum_le v W C
    refine ⟨?_, hU⟩
    intro Y hY
    have hY' := hCW hY
    rw [Finset.mem_insert] at hY'
    rcases hY' with rfl | hYW
    · exfalso
      apply hX
      rw [← hU]
      exact Finset.subset_biUnion_of_mem id hY
    · exact hYW

lemma coverNum_insert_empty (v : Fin 4) (W : Finset (Finset (Fin 14))) (hW : W0 ⊆ W) :
    coverNum v (insert ∅ W) = coverNum v W := by
  apply le_antisymm
  · exact coverNum_mono v W (insert ∅ W) hW (Finset.subset_insert ∅ W)
  · obtain ⟨C, ⟨hCW, hU⟩, hcard⟩ := exists_min_cover v (insert ∅ W) (hW.trans (Finset.subset_insert ∅ W))
    have hle : coverNum v W ≤ (C.erase ∅).card := by
      apply coverNum_le v W (C.erase ∅)
      refine ⟨?_, ?_⟩
      · intro Y hY
        have hYne : Y ≠ ∅ := (Finset.mem_erase.mp hY).1
        have hY' := hCW (Finset.mem_erase.mp hY).2
        rw [Finset.mem_insert] at hY'
        exact hY'.resolve_left hYne
      · rw [← hU]
        ext p
        simp only [Finset.mem_biUnion, id_eq, Finset.mem_erase]
        constructor
        · rintro ⟨Y, ⟨_, hYC⟩, hpY⟩
          exact ⟨Y, hYC, hpY⟩
        · rintro ⟨Y, hYC, hpY⟩
          exact ⟨Y, ⟨fun h => by subst h; exact Finset.notMem_empty p hpY, hYC⟩, hpY⟩
    exact le_trans hle (le_trans (Finset.card_erase_le) (le_of_eq hcard))

lemma coverNum_insert_union (v : Fin 4) (W : Finset (Finset (Fin 14))) (hW : W0 ⊆ W)
    (A B : Finset (Fin 14)) (hA : A = ∅ ∨ A ∈ W) (hB : B = ∅ ∨ B ∈ W) :
    coverNum v W ≤ coverNum v (insert (A ∪ B) W) + 1 := by
  obtain ⟨C, ⟨hCW, hU⟩, hcard⟩ :=
    exists_min_cover v (insert (A ∪ B) W) (hW.trans (Finset.subset_insert (A ∪ B) W))
  rw [← hcard]
  by_cases hmem : A ∪ B ∈ C
  · let partA : Finset (Finset (Fin 14)) := if A = ∅ then ∅ else {A}
    let partB : Finset (Finset (Fin 14)) := if B = ∅ then ∅ else {B}
    let C' : Finset (Finset (Fin 14)) := (C.erase (A ∪ B)) ∪ partA ∪ partB
    have hcov : isCover v W C' := by
      refine ⟨?_, ?_⟩
      · intro Y hY
        simp only [C', partA, partB, Finset.mem_union, Finset.mem_erase] at hY
        rcases hY with (⟨hYne, hYC⟩ | hYA) | hYB
        · exact (Finset.mem_insert.mp (hCW hYC)).resolve_left hYne
        · split_ifs at hYA with hA0
          · exact False.elim (Finset.notMem_empty Y hYA)
          · rw [Finset.mem_singleton.mp hYA]
            exact hA.resolve_left hA0
        · split_ifs at hYB with hB0
          · exact False.elim (Finset.notMem_empty Y hYB)
          · rw [Finset.mem_singleton.mp hYB]
            exact hB.resolve_left hB0
      · rw [← hU]
        ext p
        simp only [C', partA, partB, Finset.mem_biUnion, id_eq, Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro ⟨Y, (⟨_, hYC⟩ | hYA) | hYB, hpY⟩
          · exact ⟨Y, hYC, hpY⟩
          · split_ifs at hYA with hA0
            · exact False.elim (Finset.notMem_empty Y hYA)
            · rw [Finset.mem_singleton.mp hYA] at hpY
              exact ⟨A ∪ B, hmem, Finset.mem_union_left B hpY⟩
          · split_ifs at hYB with hB0
            · exact False.elim (Finset.notMem_empty Y hYB)
            · rw [Finset.mem_singleton.mp hYB] at hpY
              exact ⟨A ∪ B, hmem, Finset.mem_union_right A hpY⟩
        · rintro ⟨Y, hYC, hpY⟩
          by_cases hYeq : Y = A ∪ B
          · subst hYeq
            rcases Finset.mem_union.mp hpY with hpA | hpB
            · have hA0 : A ≠ ∅ := fun h => by subst h; exact Finset.notMem_empty p hpA
              exact ⟨A, Or.inl (Or.inr (by simp [hA0])), hpA⟩
            · have hB0 : B ≠ ∅ := fun h => by subst h; exact Finset.notMem_empty p hpB
              exact ⟨B, Or.inr (by simp [hB0]), hpB⟩
          · exact ⟨Y, Or.inl (Or.inl ⟨hYeq, hYC⟩), hpY⟩
    have hcardC' : C'.card ≤ C.card + 1 := by
      have h1 : (C.erase (A ∪ B)).card = C.card - 1 := Finset.card_erase_of_mem hmem
      have h2 : partA.card ≤ 1 := by dsimp [partA]; split_ifs <;> simp
      have h3 : partB.card ≤ 1 := by dsimp [partB]; split_ifs <;> simp
      have hpos : 1 ≤ C.card := Finset.one_le_card.mpr ⟨A ∪ B, hmem⟩
      have hu1 : C'.card ≤ (C.erase (A ∪ B) ∪ partA).card + partB.card := Finset.card_union_le _ _
      have hu2 : (C.erase (A ∪ B) ∪ partA).card ≤ (C.erase (A ∪ B)).card + partA.card :=
        Finset.card_union_le _ _
      omega
    exact le_trans (coverNum_le v W C' hcov) hcardC'
  · have hCW' : C ⊆ W := by
      intro Y hY
      have hY' := hCW hY
      rw [Finset.mem_insert] at hY'
      exact hY'.resolve_left (fun h => hmem (h ▸ hY))
    exact le_trans (coverNum_le v W C ⟨hCW', hU⟩) (Nat.le_succ _)

def isShared (X : Finset (Fin 14)) : Prop :=
  2 ≤ X.card ∧ ∃ i j : Fin 4, i ≠ j ∧ X ⊆ target i ∧ X ⊆ target j

noncomputable def M (W : Finset (Finset (Fin 14))) : ℕ :=
  ∑ v : Fin 4, (coverNum v W - 1)

lemma M_insert_not_shared (W : Finset (Finset (Fin 14))) (hW : W0 ⊆ W)
    (A B : Finset (Fin 14)) (hA : A = ∅ ∨ A ∈ W) (hB : B = ∅ ∨ B ∈ W)
    (hns : ¬ isShared (A ∪ B)) :
    M W ≤ M (insert (A ∪ B) W) + 1 := by
  let X := A ∪ B
  change M W ≤ M (insert X W) + 1
  by_cases hcard : 2 ≤ X.card
  · have huniq : ∀ i j : Fin 4, X ⊆ target i → X ⊆ target j → i = j := by
      intro i j hi hj
      by_contra hne
      exact hns ⟨hcard, i, j, hne, hi, hj⟩
    by_cases hex : ∃ v0 : Fin 4, X ⊆ target v0
    · obtain ⟨v0, hv0⟩ := hex
      have hother : ∀ v : Fin 4, v ≠ v0 → coverNum v (insert X W) = coverNum v W := by
        intro v hv
        apply coverNum_insert_of_not_subset v W hW X
        intro hsub
        exact hv (huniq v v0 hsub hv0)
      have hv0_le : coverNum v0 W - 1 ≤ (coverNum v0 (insert X W) - 1) + 1 := by
        have h1 : coverNum v0 W ≤ coverNum v0 (insert X W) + 1 :=
          coverNum_insert_union v0 W hW A B hA hB
        have h2 := coverNum_pos v0 (insert X W) (hW.trans (Finset.subset_insert X W))
        omega
      unfold M
      have hsum1 : ∑ v : Fin 4, (coverNum v W - 1) =
          (coverNum v0 W - 1) + ∑ v ∈ Finset.univ.erase v0, (coverNum v W - 1) :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v0)).symm
      have hsum2 : ∑ v : Fin 4, (coverNum v (insert X W) - 1) =
          (coverNum v0 (insert X W) - 1) +
            ∑ v ∈ Finset.univ.erase v0, (coverNum v (insert X W) - 1) :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v0)).symm
      rw [hsum1, hsum2]
      have heq_rest : ∑ v ∈ Finset.univ.erase v0, (coverNum v (insert X W) - 1) =
          ∑ v ∈ Finset.univ.erase v0, (coverNum v W - 1) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hother v (Finset.mem_erase.mp hv).1]
      rw [heq_rest]
      omega
    · have hex' : ∀ v : Fin 4, ¬ X ⊆ target v := fun v hv => hex ⟨v, hv⟩
      have hall : ∀ v : Fin 4, coverNum v (insert X W) = coverNum v W := fun v =>
        coverNum_insert_of_not_subset v W hW X (hex' v)
      unfold M
      simp only [hall]
      omega
  · have hle1 : X.card ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
    · have hXe : X = ∅ := Finset.card_eq_zero.mp h0
      have hall : ∀ v : Fin 4, coverNum v (insert X W) = coverNum v W := fun v => by
        rw [hXe]
        exact coverNum_insert_empty v W hW
      unfold M
      simp only [hall]
      omega
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      have hXin : X ∈ W := by
        rw [hp]
        apply hW
        simp [W0]
      rw [Finset.insert_eq_of_mem hXin]
      omega

lemma phi_induction (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (S : Finset (Finset (Fin 14))) (hS : ∀ X ∈ S, isShared X)
    (W : List (Finset (Fin 14))) (hW : W0 ⊆ W.toFinset)
    (hSsub : ∀ X ∈ (gs.foldl stepSupp W).toFinset, isShared X → X ∈ S) :
    M (W.toFinset ∪ S) + (S \ W.toFinset).card ≤
      M ((gs.foldl stepSupp W).toFinset ∪ S) + (S \ (gs.foldl stepSupp W).toFinset).card +
        gs.length := by
  induction gs generalizing W with
  | nil => simp
  | cons g rest ih =>
    have hg : g.inputs.length ≤ 2 := hgs g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ rest, g'.inputs.length ≤ 2 := fun g' hg' =>
      hgs g' (List.mem_cons_of_mem _ hg')
    simp only [List.foldl_cons, List.length_cons]
    let W1 := stepSupp W g
    have hW1 : W0 ⊆ W1.toFinset := hW.trans (by
      intro s hs
      simp only [W1, stepSupp, List.toFinset_append, Finset.mem_union]
      exact Or.inl hs)
    have hIH := ih hrest W1 hW1 hSsub
    have hW1set : W1.toFinset = insert (gateSupp W g) W.toFinset := by
      simp [W1, stepSupp, Finset.union_comm]
    have hstep : M (W.toFinset ∪ S) + (S \ W.toFinset).card ≤
        M (W1.toFinset ∪ S) + (S \ W1.toFinset).card + 1 := by
      rw [hW1set]
      by_cases hX : gateSupp W g ∈ S
      · have hu : insert (gateSupp W g) W.toFinset ∪ S = W.toFinset ∪ S := by
          ext Y
          simp only [Finset.mem_union, Finset.mem_insert]
          constructor
          · rintro ((rfl | hY) | hY)
            · exact Or.inr hX
            · exact Or.inl hY
            · exact Or.inr hY
          · rintro (hY | hY)
            · exact Or.inl (Or.inr hY)
            · exact Or.inr hY
        rw [hu]
        have hdiff : S \ W.toFinset ⊆ insert (gateSupp W g) (S \ insert (gateSupp W g) W.toFinset) := by
          intro Y hY
          simp only [Finset.mem_sdiff, Finset.mem_insert] at hY ⊢
          by_cases hYe : Y = gateSupp W g
          · exact Or.inl hYe
          · exact Or.inr ⟨hY.1, fun h => h.elim hYe hY.2⟩
        have hc := Finset.card_le_card hdiff
        have hc2 := Finset.card_insert_le (gateSupp W g) (S \ insert (gateSupp W g) W.toFinset)
        omega
      · have hXmem : gateSupp W g ∈ (rest.foldl stepSupp W1).toFinset := by
          apply foldl_stepSupp_subset rest W1
          simp [W1, stepSupp]
        have hns : ¬ isShared (gateSupp W g) := fun hsh => hX (hSsub (gateSupp W g) hXmem hsh)
        have hdiff : S \ insert (gateSupp W g) W.toFinset = S \ W.toFinset := by
          ext Y
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hYS, hYn⟩
            exact ⟨hYS, fun hYW => hYn (Or.inr hYW)⟩
          · rintro ⟨hYS, hYn⟩
            exact ⟨hYS, fun h => h.elim (fun heq => hX (heq ▸ hYS)) hYn⟩
        rw [hdiff]
        obtain ⟨A, B, hA, hB, hAB⟩ := gateSupp_eq_union W g hg
        have hA' : A = ∅ ∨ A ∈ W.toFinset ∪ S := hA.imp id (fun h => Finset.mem_union_left S h)
        have hB' : B = ∅ ∨ B ∈ W.toFinset ∪ S := hB.imp id (fun h => Finset.mem_union_left S h)
        have hM := M_insert_not_shared (W.toFinset ∪ S) (hW.trans Finset.subset_union_left) A B hA' hB'
          (hAB ▸ hns)
        rw [← hAB, ← Finset.insert_union] at hM
        omega
    dsimp only [W1] at hIH hstep
    omega

lemma shared_triple_has_pair_aux (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (W : List (Finset (Fin 14))) (X : Finset (Fin 14))
    (hW : ∀ Z ∈ W.toFinset, Z.card ≤ 1 ∨ ¬ Z ⊆ X)
    (hXmem : X ∈ (gs.foldl stepSupp W).toFinset) (hXcard : X.card = 3) :
    ∃ Y ∈ (gs.foldl stepSupp W).toFinset, Y ⊆ X ∧ Y.card = 2 := by
  induction gs generalizing W with
  | nil =>
    rcases hW X hXmem with h1 | hns
    · omega
    · exact False.elim (hns Finset.Subset.rfl)
  | cons g rest ih =>
    have hg : g.inputs.length ≤ 2 := hgs g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ rest, g'.inputs.length ≤ 2 := fun g' hg' =>
      hgs g' (List.mem_cons_of_mem _ hg')
    simp only [List.foldl_cons] at hXmem ⊢
    by_cases hsub : gateSupp W g ⊆ X
    · by_cases h2 : (gateSupp W g).card = 2
      · refine ⟨gateSupp W g, ?_, hsub, h2⟩
        apply foldl_stepSupp_subset rest (stepSupp W g)
        simp [stepSupp]
      · by_cases h1 : (gateSupp W g).card ≤ 1
        · apply ih hrest (stepSupp W g) _ hXmem
          intro Z hZ
          simp only [stepSupp, List.toFinset_append, Finset.mem_union,
            List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
            Finset.notMem_empty, or_false] at hZ
          exact hZ.elim (hW Z) (fun h => h ▸ Or.inl h1)
        · have hle3 : (gateSupp W g).card ≤ X.card := Finset.card_le_card hsub
          have heqX : gateSupp W g = X := Finset.eq_of_subset_of_card_le hsub (by omega)
          obtain ⟨A, B, hA, hB, hAB⟩ := gateSupp_eq_union W g hg
          rw [heqX] at hAB
          have hAc : A.card ≤ 1 := by
            rcases hA with rfl | hAm
            · simp
            · exact (hW A hAm).resolve_right (not_not.mpr (by rw [hAB]; exact Finset.subset_union_left))
          have hBc : B.card ≤ 1 := by
            rcases hB with rfl | hBm
            · simp
            · exact (hW B hBm).resolve_right (not_not.mpr (by rw [hAB]; exact Finset.subset_union_right))
          have hcu : X.card ≤ A.card + B.card := by rw [hAB]; exact Finset.card_union_le A B
          omega
    · apply ih hrest (stepSupp W g) _ hXmem
      intro Z hZ
      simp only [stepSupp, List.toFinset_append, Finset.mem_union,
        List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hZ
      exact hZ.elim (hW Z) (fun h => h ▸ Or.inr hsub)

lemma shared_triple_has_pair (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (W : List (Finset (Fin 14))) (hW : ∀ X ∈ W.toFinset, X.card ≤ 1)
    (X : Finset (Fin 14)) (hXmem : X ∈ (gs.foldl stepSupp W).toFinset)
    (hXcard : X.card = 3) :
    ∃ Y ∈ (gs.foldl stepSupp W).toFinset, Y ⊆ X ∧ Y.card = 2 :=
  shared_triple_has_pair_aux gs hgs W X (fun Z hZ => Or.inl (hW Z hZ)) hXmem hXcard

lemma union3_card (A B C : Finset (Fin 14)) (x y z : Fin 14)
    (hAB : A ∩ B ⊆ {x}) (hAC : A ∩ C ⊆ {y}) (hBC : B ∩ C ⊆ {z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((A ∪ B ∪ C).card : ℤ) +
      (if x ∈ A ∧ x ∈ B then 1 else 0) +
      (if y ∈ A ∧ y ∈ C then 1 else 0) +
      (if z ∈ B ∧ z ∈ C then 1 else 0) =
    (A.card : ℤ) + B.card + C.card := by
  have hcard_inter : ∀ (P Q : Finset (Fin 14)) (a : Fin 14), P ∩ Q ⊆ {a} →
      ((P ∩ Q).card : ℤ) = if a ∈ P ∧ a ∈ Q then 1 else 0 := by
    intro P Q a hPQ
    by_cases ha : a ∈ P ∧ a ∈ Q
    · have heq : P ∩ Q = {a} := by
        apply Finset.Subset.antisymm hPQ
        rw [Finset.singleton_subset_iff, Finset.mem_inter]
        exact ha
      simp [heq, ha]
    · have heq : P ∩ Q = ∅ := by
        ext q
        simp only [Finset.notMem_empty, iff_false]
        intro hq
        have hqa := Finset.mem_singleton.mp (hPQ hq)
        subst hqa
        exact ha (Finset.mem_inter.mp hq)
      simp [heq, ha]
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A ∪ B) C
  have hdist : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have hdisj : Disjoint (A ∩ C) (B ∩ C) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have hqy := Finset.mem_singleton.mp (hAC hq1)
    have hqz := Finset.mem_singleton.mp (hBC hq2)
    exact hyz (hqy.symm.trans hqz)
  have h3 : ((A ∪ B) ∩ C).card = (A ∩ C).card + (B ∩ C).card := by
    rw [hdist, Finset.card_union_of_disjoint hdisj]
  have hABc := hcard_inter A B x hAB
  have hACc := hcard_inter A C y hAC
  have hBCc := hcard_inter B C z hBC
  omega

lemma group_sav_le (w x1 x2 : Fin 14) (hw1 : w ≠ x1) (hw2 : w ≠ x2) (h12 : x1 ≠ x2)
    (Sg Ci Cj : Finset (Finset (Fin 14)))
    (hSg : ∀ A ∈ Sg, A ⊆ ({w, x1, x2} : Finset (Fin 14)) ∧ 2 ≤ A.card)
    (hvalid : ({w, x1, x2} : Finset (Fin 14)) ∈ Sg →
      ∃ Y ∈ Sg, Y ⊆ ({w, x1, x2} : Finset (Fin 14)) ∧ Y.card = 2)
    (hCi : Ci ⊆ Sg) (hCj : Cj ⊆ Sg) :
    ((Ci.biUnion id).card : ℤ) - Ci.card + (((Cj.biUnion id).card : ℤ) - Cj.card) - Sg.card ≤
      (if x1 ∈ Ci.biUnion id ∧ x1 ∈ Cj.biUnion id then 1 else 0) +
      (if x2 ∈ Ci.biUnion id ∧ x2 ∈ Cj.biUnion id then 1 else 0) := by
  let G : Finset (Fin 14) := {w, x1, x2}
  have hGcard : G.card = 3 := by
    simp [G, hw1, hw2, h12]
  have hUsub : ∀ D : Finset (Finset (Fin 14)), D ⊆ Sg → D.biUnion id ⊆ G := by
    intro D hD p hp
    obtain ⟨A, hAD, hpA⟩ := Finset.mem_biUnion.mp hp
    exact (hSg A (hD hAD)).1 hpA
  have hr_le : ∀ D : Finset (Finset (Fin 14)), D ⊆ Sg → ((D.biUnion id).card : ℤ) - D.card ≤ 2 := by
    intro D hD
    by_cases hemp : D = ∅
    · subst hemp; simp
    · have hpos : 1 ≤ D.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hemp)
      have hle3 : (D.biUnion id).card ≤ 3 := by
        rw [← hGcard]; exact Finset.card_le_card (hUsub D hD)
      omega
  have hr_eq2 : ∀ D : Finset (Finset (Fin 14)), D ⊆ Sg →
      ((D.biUnion id).card : ℤ) - D.card = 2 → D.biUnion id = G ∧ G ∈ Sg := by
    intro D hD hr
    have hne : D ≠ ∅ := by intro h; subst h; simp at hr
    have hpos : 1 ≤ D.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have hle3 : (D.biUnion id).card ≤ 3 := by
      rw [← hGcard]; exact Finset.card_le_card (hUsub D hD)
    have hU3 : (D.biUnion id).card = 3 := by omega
    have hD1 : D.card = 1 := by omega
    have hUG : D.biUnion id = G := Finset.eq_of_subset_of_card_le (hUsub D hD) (by omega)
    obtain ⟨A, hDA⟩ := Finset.card_eq_one.mp hD1
    have hAG : A = G := by
      rw [hDA, Finset.singleton_biUnion, id_eq] at hUG
      exact hUG
    refine ⟨hUG, ?_⟩
    rw [← hAG]
    exact hD (hDA ▸ Finset.mem_singleton_self A)
  have hr_ge1 : ∀ D : Finset (Finset (Fin 14)), D ⊆ Sg →
      1 ≤ ((D.biUnion id).card : ℤ) - D.card → x1 ∈ D.biUnion id ∨ x2 ∈ D.biUnion id := by
    intro D hD hr
    have hne : D ≠ ∅ := by intro h; subst h; simp at hr
    have hpos : 1 ≤ D.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have hge2 : 2 ≤ (D.biUnion id).card := by omega
    by_contra hneither
    have hn1 : x1 ∉ D.biUnion id := fun h => hneither (Or.inl h)
    have hn2 : x2 ∉ D.biUnion id := fun h => hneither (Or.inr h)
    have hsubw : D.biUnion id ⊆ {w} := by
      intro p hp
      have hpG := hUsub D hD hp
      simp only [G, Finset.mem_insert, Finset.mem_singleton] at hpG
      rcases hpG with rfl | rfl | rfl
      · exact Finset.mem_singleton_self p
      · exact False.elim (hn1 hp)
      · exact False.elim (hn2 hp)
    have hle1 : (D.biUnion id).card ≤ 1 := by
      simpa using Finset.card_le_card hsubw
    omega
  have hG_ge2 : G ∈ Sg → 2 ≤ Sg.card := by
    intro hGm
    obtain ⟨Y, hYS, _, hY2⟩ := hvalid hGm
    have hYne : Y ≠ G := fun h => by rw [h, hGcard] at hY2; omega
    have hsub : ({Y, G} : Finset (Finset (Fin 14))) ⊆ Sg := by
      intro A hA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · exact hYS
      · exact hGm
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hYne] at hc
    exact hc
  let ri : ℤ := ((Ci.biUnion id).card : ℤ) - Ci.card
  let rj : ℤ := ((Cj.biUnion id).card : ℤ) - Cj.card
  have hri : ri ≤ 2 := hr_le Ci hCi
  have hrj : rj ≤ 2 := hr_le Cj hCj
  have hCi_le : Ci.card ≤ Sg.card := Finset.card_le_card hCi
  have hCj_le : Cj.card ≤ Sg.card := Finset.card_le_card hCj
  by_cases hle0 : ri + rj - Sg.card ≤ 0
  · have hnn : (0 : ℤ) ≤ (if x1 ∈ Ci.biUnion id ∧ x1 ∈ Cj.biUnion id then 1 else 0) +
        (if x2 ∈ Ci.biUnion id ∧ x2 ∈ Cj.biUnion id then 1 else 0) := by
      split_ifs <;> omega
    exact le_trans hle0 hnn
  · by_cases hS0 : Sg.card = 0
    · have hCi0 : Ci = ∅ := Finset.card_eq_zero.mp (by omega)
      have hCj0 : Cj = ∅ := Finset.card_eq_zero.mp (by omega)
      simp only [ri, rj, hCi0, hCj0, Finset.biUnion_empty, Finset.card_empty, hS0] at hle0
      omega
    · by_cases hS1 : Sg.card = 1
      · have hGnot : G ∉ Sg := fun hGm => by have := hG_ge2 hGm; omega
        have hri1 : ri ≤ 1 := by
          by_contra hgt
          have heq2 : ri = 2 := by omega
          exact hGnot (hr_eq2 Ci hCi heq2).2
        have hrj1 : rj ≤ 1 := by
          by_contra hgt
          have heq2 : rj = 2 := by omega
          exact hGnot (hr_eq2 Cj hCj heq2).2
        have hri_eq1 : ri = 1 := by omega
        have hrj_eq1 : rj = 1 := by omega
        have hCi_ne : Ci ≠ ∅ := by intro h; simp [ri, h] at hri_eq1
        have hCj_ne : Cj ≠ ∅ := by intro h; simp [rj, h] at hrj_eq1
        have hCi_eq : Ci = Sg := Finset.eq_of_subset_of_card_le hCi (by
          have := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hCi_ne); omega)
        have hCj_eq : Cj = Sg := Finset.eq_of_subset_of_card_le hCj (by
          have := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hCj_ne); omega)
        have hor := hr_ge1 Ci hCi (by omega)
        have h1eq : ((Ci.biUnion id).card : ℤ) - Ci.card + (((Cj.biUnion id).card : ℤ) - Cj.card) - Sg.card = 1 := by
          change ri + rj - Sg.card = 1; omega
        rw [h1eq]
        rcases hor with h1 | h2
        · have h1j : x1 ∈ Cj.biUnion id := by rw [hCj_eq, ← hCi_eq]; exact h1
          have h1' : x1 ∈ Ci.biUnion id ∧ x1 ∈ Cj.biUnion id := ⟨h1, h1j⟩
          split_ifs <;> omega
        · have h2j : x2 ∈ Cj.biUnion id := by rw [hCj_eq, ← hCi_eq]; exact h2
          have h2' : x2 ∈ Ci.biUnion id ∧ x2 ∈ Cj.biUnion id := ⟨h2, h2j⟩
          split_ifs <;> omega
      · have hS2 : 2 ≤ Sg.card := by omega
        by_cases hboth : ri = 2 ∧ rj = 2
        · have hUiG := (hr_eq2 Ci hCi hboth.1).1
          have hUjG := (hr_eq2 Cj hCj hboth.2).1
          have hx1i : x1 ∈ Ci.biUnion id := by rw [hUiG]; simp [G]
          have hx1j : x1 ∈ Cj.biUnion id := by rw [hUjG]; simp [G]
          have hx2i : x2 ∈ Ci.biUnion id := by rw [hUiG]; simp [G]
          have hx2j : x2 ∈ Cj.biUnion id := by rw [hUjG]; simp [G]
          have h1 : x1 ∈ Ci.biUnion id ∧ x1 ∈ Cj.biUnion id := ⟨hx1i, hx1j⟩
          have h2 : x2 ∈ Ci.biUnion id ∧ x2 ∈ Cj.biUnion id := ⟨hx2i, hx2j⟩
          split_ifs <;> omega
        · have h1or2 : (ri = 2 ∧ 1 ≤ rj) ∨ (rj = 2 ∧ 1 ≤ ri) := by omega
          rcases h1or2 with ⟨hi2, hj1⟩ | ⟨hj2, hi1⟩
          · have hUiG := (hr_eq2 Ci hCi hi2).1
            have hor := hr_ge1 Cj hCj hj1
            have hx1i : x1 ∈ Ci.biUnion id := by rw [hUiG]; simp [G]
            have hx2i : x2 ∈ Ci.biUnion id := by rw [hUiG]; simp [G]
            rcases hor with hx1j | hx2j
            · have h1 : x1 ∈ Ci.biUnion id ∧ x1 ∈ Cj.biUnion id := ⟨hx1i, hx1j⟩
              split_ifs <;> omega
            · have h2 : x2 ∈ Ci.biUnion id ∧ x2 ∈ Cj.biUnion id := ⟨hx2i, hx2j⟩
              split_ifs <;> omega
          · have hUjG := (hr_eq2 Cj hCj hj2).1
            have hor := hr_ge1 Ci hCi hi1
            have hx1j : x1 ∈ Cj.biUnion id := by rw [hUjG]; simp [G]
            have hx2j : x2 ∈ Cj.biUnion id := by rw [hUjG]; simp [G]
            rcases hor with hx1i | hx2i
            · have h1 : x1 ∈ Ci.biUnion id ∧ x1 ∈ Cj.biUnion id := ⟨hx1i, hx1j⟩
              split_ifs <;> omega
            · have h2 : x2 ∈ Ci.biUnion id ∧ x2 ∈ Cj.biUnion id := ⟨hx2i, hx2j⟩
              split_ifs <;> omega

lemma tri_le_one (a1 a2 b1 b2 c1 c2 : Prop) [Decidable a1] [Decidable a2]
    [Decidable b1] [Decidable b2] [Decidable c1] [Decidable c2] :
    (if a1 ∧ b1 then (1 : ℤ) else 0) +
    (if a2 ∧ c1 then 1 else 0) +
    (if b2 ∧ c2 then 1 else 0) -
    ((if a1 ∧ a2 then 1 else 0) +
     (if b1 ∧ b2 then 1 else 0) +
     (if c1 ∧ c2 then 1 else 0)) ≤ 1 := by
  by_cases h1 : a1 ∧ b1 <;> by_cases h2 : a2 ∧ c1 <;> by_cases h3 : b2 ∧ c2
  · have ha : a1 ∧ a2 := ⟨h1.1, h2.1⟩
    have hb : b1 ∧ b2 := ⟨h1.2, h3.1⟩
    have hc : c1 ∧ c2 := ⟨h2.2, h3.2⟩
    simp [h1, h2, h3, ha, hb, hc]
  · have ha : a1 ∧ a2 := ⟨h1.1, h2.1⟩
    simp only [h1, h2, h3, ha, ite_true, ite_false]
    split_ifs <;> omega
  · have hb : b1 ∧ b2 := ⟨h1.2, h3.1⟩
    simp only [h1, h2, h3, hb, ite_true, ite_false]
    split_ifs <;> omega
  · simp only [h1, h2, h3, ite_true, ite_false]
    split_ifs <;> omega
  · have hc : c1 ∧ c2 := ⟨h2.2, h3.2⟩
    simp only [h1, h2, h3, hc, ite_true, ite_false]
    split_ifs <;> omega
  · simp only [h1, h2, h3, ite_true, ite_false]
    split_ifs <;> omega
  · simp only [h1, h2, h3, ite_true, ite_false]
    split_ifs <;> omega
  · simp only [h1, h2, h3, ite_true, ite_false]
    split_ifs <;> omega

lemma target_card (v : Fin 4) : (target v).card = 7 := by
  fin_cases v <;> decide

lemma inter_01 : target 0 ∩ target 1 = {(2 : Fin 14), 6, 10} := by
  rw [target_0, target_1]; decide
lemma inter_02 : target 0 ∩ target 2 = {(4 : Fin 14), 6, 12} := by
  rw [target_0, target_2]; decide
lemma inter_03 : target 0 ∩ target 3 = {(8 : Fin 14), 10, 12} := by
  rw [target_0, target_3]; decide
lemma inter_12 : target 1 ∩ target 2 = {(5 : Fin 14), 6, 13} := by
  rw [target_1, target_2]; decide
lemma inter_13 : target 1 ∩ target 3 = {(9 : Fin 14), 10, 13} := by
  rw [target_1, target_3]; decide
lemma inter_23 : target 2 ∩ target 3 = {(11 : Fin 14), 12, 13} := by
  rw [target_2, target_3]; decide

lemma pair_disjoint (S : Finset (Finset (Fin 14))) (hS : ∀ A ∈ S, isShared A)
    (P Q : Finset (Fin 14)) (hPQ : (P ∩ Q).card ≤ 1) :
    Disjoint (S.filter (fun A => A ⊆ P)) (S.filter (fun A => A ⊆ Q)) := by
  rw [Finset.disjoint_left]
  intro A hA1 hA2
  have h2 : 2 ≤ A.card := (hS A (Finset.mem_filter.mp hA1).1).1
  have hsub : A ⊆ P ∩ Q :=
    Finset.subset_inter (Finset.mem_filter.mp hA1).2 (Finset.mem_filter.mp hA2).2
  have hc := Finset.card_le_card hsub
  omega

lemma target_cover_bound (v i1 j1 i2 j2 i3 j3 : Fin 4) (x y z : Fin 14)
    (S Cv : Finset (Finset (Fin 14)))
    (hS : ∀ A ∈ S, isShared A)
    (hcov : isCover v (W0 ∪ S) Cv)
    (hpart : ∀ A ∈ S, A ⊆ target v →
      A ⊆ target i1 ∩ target j1 ∨ A ⊆ target i2 ∩ target j2 ∨ A ⊆ target i3 ∩ target j3)
    (hAB : (target i1 ∩ target j1) ∩ (target i2 ∩ target j2) ⊆ {x})
    (hAC : (target i1 ∩ target j1) ∩ (target i3 ∩ target j3) ⊆ {y})
    (hBC : (target i2 ∩ target j2) ∩ (target i3 ∩ target j3) ⊆ {z})
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let S1 := S.filter (fun A => A ⊆ target i1 ∩ target j1)
    let S2 := S.filter (fun A => A ⊆ target i2 ∩ target j2)
    let S3 := S.filter (fun A => A ⊆ target i3 ∩ target j3)
    let C1 := Cv ∩ S1
    let C2 := Cv ∩ S2
    let C3 := Cv ∩ S3
    let U1 := C1.biUnion id
    let U2 := C2.biUnion id
    let U3 := C3.biUnion id
    (7 : ℤ) ≤ (Cv.card : ℤ) +
      ((U1.card : ℤ) - C1.card) + ((U2.card : ℤ) - C2.card) + ((U3.card : ℤ) - C3.card) -
      ((if x ∈ U1 ∧ x ∈ U2 then 1 else 0) +
       (if y ∈ U1 ∧ y ∈ U3 then 1 else 0) +
       (if z ∈ U2 ∧ z ∈ U3 then 1 else 0)) := by
  intro S1 S2 S3 C1 C2 C3 U1 U2 U3
  let C0 := Cv ∩ W0
  have hd01 : Disjoint C0 C1 := by
    rw [Finset.disjoint_left]
    intro A hA0 hA1
    have h1' : A.card = 1 := by
      have hW := (Finset.mem_inter.mp hA0).2
      simp only [W0, Finset.mem_image, Finset.mem_univ, true_and] at hW
      obtain ⟨p, rfl⟩ := hW
      simp
    have h2' : 2 ≤ A.card := (hS A (Finset.mem_filter.mp (Finset.mem_inter.mp hA1).2).1).1
    omega
  have hd02 : Disjoint C0 C2 := by
    rw [Finset.disjoint_left]
    intro A hA0 hA2
    have h1' : A.card = 1 := by
      have hW := (Finset.mem_inter.mp hA0).2
      simp only [W0, Finset.mem_image, Finset.mem_univ, true_and] at hW
      obtain ⟨p, rfl⟩ := hW
      simp
    have h2' : 2 ≤ A.card := (hS A (Finset.mem_filter.mp (Finset.mem_inter.mp hA2).2).1).1
    omega
  have hd03 : Disjoint C0 C3 := by
    rw [Finset.disjoint_left]
    intro A hA0 hA3
    have h1' : A.card = 1 := by
      have hW := (Finset.mem_inter.mp hA0).2
      simp only [W0, Finset.mem_image, Finset.mem_univ, true_and] at hW
      obtain ⟨p, rfl⟩ := hW
      simp
    have h2' : 2 ≤ A.card := (hS A (Finset.mem_filter.mp (Finset.mem_inter.mp hA3).2).1).1
    omega
  have hd12 : Disjoint C1 C2 :=
    (pair_disjoint S hS _ _ (by simpa using Finset.card_le_card hAB)).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hd13 : Disjoint C1 C3 :=
    (pair_disjoint S hS _ _ (by simpa using Finset.card_le_card hAC)).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hd23 : Disjoint C2 C3 :=
    (pair_disjoint S hS _ _ (by simpa using Finset.card_le_card hBC)).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hCv_eq : Cv = C0 ∪ C1 ∪ C2 ∪ C3 := by
    ext A
    simp only [C0, C1, C2, C3, S1, S2, S3, Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    constructor
    · intro hAC
      have hAsub : A ⊆ target v := by
        rw [← hcov.2]
        exact Finset.subset_biUnion_of_mem id hAC
      rcases Finset.mem_union.mp (hcov.1 hAC) with hAW | hAS
      · exact Or.inl (Or.inl (Or.inl ⟨hAC, hAW⟩))
      · rcases hpart A hAS hAsub with h1' | h2' | h3'
        · exact Or.inl (Or.inl (Or.inr ⟨hAC, hAS, h1'⟩))
        · exact Or.inl (Or.inr ⟨hAC, hAS, h2'⟩)
        · exact Or.inr ⟨hAC, hAS, h3'⟩
    · rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hCv_card : Cv.card = C0.card + C1.card + C2.card + C3.card := by
    rw [hCv_eq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint]
    · exact hd01
    · exact Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩
    · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hd03, hd13⟩, hd23⟩
  have hTsub : target v ⊆ C0.biUnion id ∪ (U1 ∪ U2 ∪ U3) := by
    rw [← hcov.2, hCv_eq]
    intro p hp
    simp only [U1, U2, U3, Finset.mem_biUnion, id_eq, Finset.mem_union] at hp ⊢
    obtain ⟨A, ((hA | hA) | hA) | hA, hpA⟩ := hp
    · exact Or.inl ⟨A, hA, hpA⟩
    · exact Or.inr (Or.inl (Or.inl ⟨A, hA, hpA⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨A, hA, hpA⟩))
    · exact Or.inr (Or.inr ⟨A, hA, hpA⟩)
  have hC0_card : (C0.biUnion id).card ≤ C0.card := by
    calc (C0.biUnion id).card ≤ ∑ A ∈ C0, A.card := Finset.card_biUnion_le
      _ = ∑ _A ∈ C0, 1 := by
        apply Finset.sum_congr rfl
        intro A hA
        have hW := (Finset.mem_inter.mp hA).2
        simp only [W0, Finset.mem_image, Finset.mem_univ, true_and] at hW
        obtain ⟨p, rfl⟩ := hW
        simp
      _ = C0.card := by simp
  have h7 : 7 ≤ C0.card + (U1 ∪ U2 ∪ U3).card := by
    have ht7 : (target v).card = 7 := target_card v
    have h1' := Finset.card_le_card hTsub
    have h2' := Finset.card_union_le (C0.biUnion id) (U1 ∪ U2 ∪ U3)
    omega
  have hU1sub : U1 ⊆ target i1 ∩ target j1 := by
    intro p hp
    obtain ⟨A, hA, hpA⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hA).2).2 hpA
  have hU2sub : U2 ⊆ target i2 ∩ target j2 := by
    intro p hp
    obtain ⟨A, hA, hpA⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hA).2).2 hpA
  have hU3sub : U3 ⊆ target i3 ∩ target j3 := by
    intro p hp
    obtain ⟨A, hA, hpA⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hA).2).2 hpA
  have hu3 := union3_card U1 U2 U3 x y z
    ((Finset.inter_subset_inter hU1sub hU2sub).trans hAB)
    ((Finset.inter_subset_inter hU1sub hU3sub).trans hAC)
    ((Finset.inter_subset_inter hU2sub hU3sub).trans hBC)
    hxy hxz hyz
  omega

lemma combine_14
    {c0 c1 c2 c3 s01 s02 s03 s12 s13 s23
      r0_01 r0_02 r0_03 r1_01 r1_12 r1_13 r2_02 r2_12 r2_23 r3_03 r3_13 r3_23
      o0_6 o0_10 o0_12 o1_6 o1_10 o1_13 o2_6 o2_12 o2_13 o3_10 o3_12 o3_13
      m01_6 m01_10 m02_6 m02_12 m03_10 m03_12 m12_6 m12_13 m13_10 m13_13 m23_12 m23_13 : ℤ}
    (hb0 : 7 ≤ c0 + r0_01 + r0_02 + r0_03 - (o0_6 + o0_10 + o0_12))
    (hb1 : 7 ≤ c1 + r1_01 + r1_12 + r1_13 - (o1_6 + o1_10 + o1_13))
    (hb2 : 7 ≤ c2 + r2_02 + r2_12 + r2_23 - (o2_6 + o2_12 + o2_13))
    (hb3 : 7 ≤ c3 + r3_03 + r3_13 + r3_23 - (o3_10 + o3_12 + o3_13))
    (hg01 : r0_01 + r1_01 - s01 ≤ m01_6 + m01_10)
    (hg02 : r0_02 + r2_02 - s02 ≤ m02_6 + m02_12)
    (hg03 : r0_03 + r3_03 - s03 ≤ m03_10 + m03_12)
    (hg12 : r1_12 + r2_12 - s12 ≤ m12_6 + m12_13)
    (hg13 : r1_13 + r3_13 - s13 ≤ m13_10 + m13_13)
    (hg23 : r2_23 + r3_23 - s23 ≤ m23_12 + m23_13)
    (ht6 : m01_6 + m02_6 + m12_6 - (o0_6 + o1_6 + o2_6) ≤ 1)
    (ht10 : m01_10 + m03_10 + m13_10 - (o0_10 + o1_10 + o3_10) ≤ 1)
    (ht12 : m02_12 + m03_12 + m23_12 - (o0_12 + o2_12 + o3_12) ≤ 1)
    (ht13 : m12_13 + m13_13 + m23_13 - (o1_13 + o2_13 + o3_13) ≤ 1) :
    24 ≤ c0 + c1 + c2 + c3 + (s01 + s02 + s03 + s12 + s13 + s23) := by
  have h1 := add_le_add (add_le_add hb0 hb1) (add_le_add hb2 hb3)
  have h2 := add_le_add (add_le_add (add_le_add hg01 hg02) (add_le_add hg03 hg12))
    (add_le_add hg13 hg23)
  have h3 := add_le_add (add_le_add ht6 ht10) (add_le_add ht12 ht13)
  clear hb0 hb1 hb2 hb3 hg01 hg02 hg03 hg12 hg13 hg23 ht6 ht10 ht12 ht13
  omega

lemma combinatorial_bound (S : Finset (Finset (Fin 14)))
    (hS : ∀ A ∈ S, isShared A)
    (hvalid : ∀ A ∈ S, A.card = 3 → ∃ Y ∈ S, Y ⊆ A ∧ Y.card = 2)
    (C : Fin 4 → Finset (Finset (Fin 14)))
    (hC : ∀ v : Fin 4, isCover v (W0 ∪ S) (C v)) :
    (24 : ℤ) ≤ (∑ v : Fin 4, ((C v).card : ℤ)) + S.card := by
  let S01 := S.filter (fun A => A ⊆ target 0 ∩ target 1)
  let S02 := S.filter (fun A => A ⊆ target 0 ∩ target 2)
  let S03 := S.filter (fun A => A ⊆ target 0 ∩ target 3)
  let S12 := S.filter (fun A => A ⊆ target 1 ∩ target 2)
  let S13 := S.filter (fun A => A ⊆ target 1 ∩ target 3)
  let S23 := S.filter (fun A => A ⊆ target 2 ∩ target 3)
  have hS_eq : S = S01 ∪ S02 ∪ S03 ∪ S12 ∪ S13 ∪ S23 := by
    ext A
    simp only [S01, S02, S03, S12, S13, S23, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hAS
      obtain ⟨_, ⟨i, hi⟩, ⟨j, hj⟩, hij, hAi, hAj⟩ := hS A hAS
      match i, hi, j, hj with
      | 0, _, 0, _ | 1, _, 1, _ | 2, _, 2, _ | 3, _, 3, _ => exact False.elim (hij rfl)
      | 0, _, 1, _ => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hAS, Finset.subset_inter hAi hAj⟩))))
      | 1, _, 0, _ => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hAS, Finset.subset_inter hAj hAi⟩))))
      | 0, _, 2, _ => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAi hAj⟩))))
      | 2, _, 0, _ => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAj hAi⟩))))
      | 0, _, 3, _ => exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAi hAj⟩)))
      | 3, _, 0, _ => exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAj hAi⟩)))
      | 1, _, 2, _ => exact Or.inl (Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAi hAj⟩))
      | 2, _, 1, _ => exact Or.inl (Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAj hAi⟩))
      | 1, _, 3, _ => exact Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAi hAj⟩)
      | 3, _, 1, _ => exact Or.inl (Or.inr ⟨hAS, Finset.subset_inter hAj hAi⟩)
      | 2, _, 3, _ => exact Or.inr ⟨hAS, Finset.subset_inter hAi hAj⟩
      | 3, _, 2, _ => exact Or.inr ⟨hAS, Finset.subset_inter hAj hAi⟩
    · rintro (((((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hS_card : S.card = S01.card + S02.card + S03.card + S12.card + S13.card + S23.card := by
    have d01_02 : Disjoint S01 S02 := pair_disjoint S hS _ _ (by rw [inter_01, inter_02]; decide)
    have d01_03 : Disjoint S01 S03 := pair_disjoint S hS _ _ (by rw [inter_01, inter_03]; decide)
    have d01_12 : Disjoint S01 S12 := pair_disjoint S hS _ _ (by rw [inter_01, inter_12]; decide)
    have d01_13 : Disjoint S01 S13 := pair_disjoint S hS _ _ (by rw [inter_01, inter_13]; decide)
    have d01_23 : Disjoint S01 S23 := pair_disjoint S hS _ _ (by rw [inter_01, inter_23]; decide)
    have d02_03 : Disjoint S02 S03 := pair_disjoint S hS _ _ (by rw [inter_02, inter_03]; decide)
    have d02_12 : Disjoint S02 S12 := pair_disjoint S hS _ _ (by rw [inter_02, inter_12]; decide)
    have d02_13 : Disjoint S02 S13 := pair_disjoint S hS _ _ (by rw [inter_02, inter_13]; decide)
    have d02_23 : Disjoint S02 S23 := pair_disjoint S hS _ _ (by rw [inter_02, inter_23]; decide)
    have d03_12 : Disjoint S03 S12 := pair_disjoint S hS _ _ (by rw [inter_03, inter_12]; decide)
    have d03_13 : Disjoint S03 S13 := pair_disjoint S hS _ _ (by rw [inter_03, inter_13]; decide)
    have d03_23 : Disjoint S03 S23 := pair_disjoint S hS _ _ (by rw [inter_03, inter_23]; decide)
    have d12_13 : Disjoint S12 S13 := pair_disjoint S hS _ _ (by rw [inter_12, inter_13]; decide)
    have d12_23 : Disjoint S12 S23 := pair_disjoint S hS _ _ (by rw [inter_12, inter_23]; decide)
    have d13_23 : Disjoint S13 S23 := pair_disjoint S hS _ _ (by rw [inter_13, inter_23]; decide)
    rw [hS_eq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · exact d01_02
    · exact Finset.disjoint_union_left.mpr ⟨d01_03, d02_03⟩
    · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d01_12, d02_12⟩, d03_12⟩
    · exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d01_13, d02_13⟩, d03_13⟩, d12_13⟩
    · exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d01_23, d02_23⟩, d03_23⟩, d12_23⟩, d13_23⟩
  have hpart0 : ∀ A ∈ S, A ⊆ target 0 →
      A ⊆ target 0 ∩ target 1 ∨ A ⊆ target 0 ∩ target 2 ∨ A ⊆ target 0 ∩ target 3 := by
    intro A hAS hA0
    obtain ⟨_, ⟨i, hi⟩, ⟨j, hj⟩, hij, hAi, hAj⟩ := hS A hAS
    match i, hi, j, hj with
    | 0, _, 0, _ => exact False.elim (hij rfl)
    | 0, _, 1, _ => exact Or.inl (Finset.subset_inter hA0 hAj)
    | 0, _, 2, _ => exact Or.inr (Or.inl (Finset.subset_inter hA0 hAj))
    | 0, _, 3, _ => exact Or.inr (Or.inr (Finset.subset_inter hA0 hAj))
    | 1, _, _, _ => exact Or.inl (Finset.subset_inter hA0 hAi)
    | 2, _, _, _ => exact Or.inr (Or.inl (Finset.subset_inter hA0 hAi))
    | 3, _, _, _ => exact Or.inr (Or.inr (Finset.subset_inter hA0 hAi))
  have hpart1 : ∀ A ∈ S, A ⊆ target 1 →
      A ⊆ target 0 ∩ target 1 ∨ A ⊆ target 1 ∩ target 2 ∨ A ⊆ target 1 ∩ target 3 := by
    intro A hAS hA1
    obtain ⟨_, ⟨i, hi⟩, ⟨j, hj⟩, hij, hAi, hAj⟩ := hS A hAS
    match i, hi, j, hj with
    | 1, _, 1, _ => exact False.elim (hij rfl)
    | 1, _, 0, _ => exact Or.inl (Finset.subset_inter hAj hA1)
    | 1, _, 2, _ => exact Or.inr (Or.inl (Finset.subset_inter hA1 hAj))
    | 1, _, 3, _ => exact Or.inr (Or.inr (Finset.subset_inter hA1 hAj))
    | 0, _, _, _ => exact Or.inl (Finset.subset_inter hAi hA1)
    | 2, _, _, _ => exact Or.inr (Or.inl (Finset.subset_inter hA1 hAi))
    | 3, _, _, _ => exact Or.inr (Or.inr (Finset.subset_inter hA1 hAi))
  have hpart2 : ∀ A ∈ S, A ⊆ target 2 →
      A ⊆ target 0 ∩ target 2 ∨ A ⊆ target 1 ∩ target 2 ∨ A ⊆ target 2 ∩ target 3 := by
    intro A hAS hA2
    obtain ⟨_, ⟨i, hi⟩, ⟨j, hj⟩, hij, hAi, hAj⟩ := hS A hAS
    match i, hi, j, hj with
    | 2, _, 2, _ => exact False.elim (hij rfl)
    | 2, _, 0, _ => exact Or.inl (Finset.subset_inter hAj hA2)
    | 2, _, 1, _ => exact Or.inr (Or.inl (Finset.subset_inter hAj hA2))
    | 2, _, 3, _ => exact Or.inr (Or.inr (Finset.subset_inter hA2 hAj))
    | 0, _, _, _ => exact Or.inl (Finset.subset_inter hAi hA2)
    | 1, _, _, _ => exact Or.inr (Or.inl (Finset.subset_inter hAi hA2))
    | 3, _, _, _ => exact Or.inr (Or.inr (Finset.subset_inter hA2 hAi))
  have hpart3 : ∀ A ∈ S, A ⊆ target 3 →
      A ⊆ target 0 ∩ target 3 ∨ A ⊆ target 1 ∩ target 3 ∨ A ⊆ target 2 ∩ target 3 := by
    intro A hAS hA3
    obtain ⟨_, ⟨i, hi⟩, ⟨j, hj⟩, hij, hAi, hAj⟩ := hS A hAS
    match i, hi, j, hj with
    | 3, _, 3, _ => exact False.elim (hij rfl)
    | 3, _, 0, _ => exact Or.inl (Finset.subset_inter hAj hA3)
    | 3, _, 1, _ => exact Or.inr (Or.inl (Finset.subset_inter hAj hA3))
    | 3, _, 2, _ => exact Or.inr (Or.inr (Finset.subset_inter hAj hA3))
    | 0, _, _, _ => exact Or.inl (Finset.subset_inter hAi hA3)
    | 1, _, _, _ => exact Or.inr (Or.inl (Finset.subset_inter hAi hA3))
    | 2, _, _, _ => exact Or.inr (Or.inr (Finset.subset_inter hAi hA3))
  have hb0 := target_cover_bound 0 0 1 0 2 0 3 6 10 12 S (C 0) hS (hC 0) hpart0
    (by rw [inter_01, inter_02]; decide) (by rw [inter_01, inter_03]; decide)
    (by rw [inter_02, inter_03]; decide) (by decide) (by decide) (by decide)
  have hb1 := target_cover_bound 1 0 1 1 2 1 3 6 10 13 S (C 1) hS (hC 1) hpart1
    (by rw [inter_01, inter_12]; decide) (by rw [inter_01, inter_13]; decide)
    (by rw [inter_12, inter_13]; decide) (by decide) (by decide) (by decide)
  have hb2 := target_cover_bound 2 0 2 1 2 2 3 6 12 13 S (C 2) hS (hC 2) hpart2
    (by rw [inter_02, inter_12]; decide) (by rw [inter_02, inter_23]; decide)
    (by rw [inter_12, inter_23]; decide) (by decide) (by decide) (by decide)
  have hb3 := target_cover_bound 3 0 3 1 3 2 3 10 12 13 S (C 3) hS (hC 3) hpart3
    (by rw [inter_03, inter_13]; decide) (by rw [inter_03, inter_23]; decide)
    (by rw [inter_13, inter_23]; decide) (by decide) (by decide) (by decide)
  have hval_sub : ∀ (i j : Fin 4) (G : Finset (Fin 14)),
      target i ∩ target j = G → G.card = 3 →
      G ∈ S.filter (fun A => A ⊆ target i ∩ target j) →
      ∃ Y ∈ S.filter (fun A => A ⊆ target i ∩ target j), Y ⊆ G ∧ Y.card = 2 := by
    intro i j G hG hGc hGm
    obtain ⟨Y, hYS, hYG, hY2⟩ := hvalid G (Finset.mem_filter.mp hGm).1 hGc
    exact ⟨Y, Finset.mem_filter.mpr ⟨hYS, hG ▸ hYG⟩, hYG, hY2⟩
  have hg01 := group_sav_le 2 6 10 (by decide) (by decide) (by decide)
    S01 (C 0 ∩ S01) (C 1 ∩ S01)
    (fun A hA => ⟨inter_01 ▸ (Finset.mem_filter.mp hA).2, (hS A (Finset.mem_filter.mp hA).1).1⟩)
    (hval_sub 0 1 {2, 6, 10} inter_01 (by decide))
    Finset.inter_subset_right Finset.inter_subset_right
  have hg02 := group_sav_le 4 6 12 (by decide) (by decide) (by decide)
    S02 (C 0 ∩ S02) (C 2 ∩ S02)
    (fun A hA => ⟨inter_02 ▸ (Finset.mem_filter.mp hA).2, (hS A (Finset.mem_filter.mp hA).1).1⟩)
    (hval_sub 0 2 {4, 6, 12} inter_02 (by decide))
    Finset.inter_subset_right Finset.inter_subset_right
  have hg03 := group_sav_le 8 10 12 (by decide) (by decide) (by decide)
    S03 (C 0 ∩ S03) (C 3 ∩ S03)
    (fun A hA => ⟨inter_03 ▸ (Finset.mem_filter.mp hA).2, (hS A (Finset.mem_filter.mp hA).1).1⟩)
    (hval_sub 0 3 {8, 10, 12} inter_03 (by decide))
    Finset.inter_subset_right Finset.inter_subset_right
  have hg12 := group_sav_le 5 6 13 (by decide) (by decide) (by decide)
    S12 (C 1 ∩ S12) (C 2 ∩ S12)
    (fun A hA => ⟨inter_12 ▸ (Finset.mem_filter.mp hA).2, (hS A (Finset.mem_filter.mp hA).1).1⟩)
    (hval_sub 1 2 {5, 6, 13} inter_12 (by decide))
    Finset.inter_subset_right Finset.inter_subset_right
  have hg13 := group_sav_le 9 10 13 (by decide) (by decide) (by decide)
    S13 (C 1 ∩ S13) (C 3 ∩ S13)
    (fun A hA => ⟨inter_13 ▸ (Finset.mem_filter.mp hA).2, (hS A (Finset.mem_filter.mp hA).1).1⟩)
    (hval_sub 1 3 {9, 10, 13} inter_13 (by decide))
    Finset.inter_subset_right Finset.inter_subset_right
  have hg23 := group_sav_le 11 12 13 (by decide) (by decide) (by decide)
    S23 (C 2 ∩ S23) (C 3 ∩ S23)
    (fun A hA => ⟨inter_23 ▸ (Finset.mem_filter.mp hA).2, (hS A (Finset.mem_filter.mp hA).1).1⟩)
    (hval_sub 2 3 {11, 12, 13} inter_23 (by decide))
    Finset.inter_subset_right Finset.inter_subset_right
  have ht6 := tri_le_one
    ((6 : Fin 14) ∈ (C 0 ∩ S01).biUnion id) ((6 : Fin 14) ∈ (C 0 ∩ S02).biUnion id)
    ((6 : Fin 14) ∈ (C 1 ∩ S01).biUnion id) ((6 : Fin 14) ∈ (C 1 ∩ S12).biUnion id)
    ((6 : Fin 14) ∈ (C 2 ∩ S02).biUnion id) ((6 : Fin 14) ∈ (C 2 ∩ S12).biUnion id)
  have ht10 := tri_le_one
    ((10 : Fin 14) ∈ (C 0 ∩ S01).biUnion id) ((10 : Fin 14) ∈ (C 0 ∩ S03).biUnion id)
    ((10 : Fin 14) ∈ (C 1 ∩ S01).biUnion id) ((10 : Fin 14) ∈ (C 1 ∩ S13).biUnion id)
    ((10 : Fin 14) ∈ (C 3 ∩ S03).biUnion id) ((10 : Fin 14) ∈ (C 3 ∩ S13).biUnion id)
  have ht12 := tri_le_one
    ((12 : Fin 14) ∈ (C 0 ∩ S02).biUnion id) ((12 : Fin 14) ∈ (C 0 ∩ S03).biUnion id)
    ((12 : Fin 14) ∈ (C 2 ∩ S02).biUnion id) ((12 : Fin 14) ∈ (C 2 ∩ S23).biUnion id)
    ((12 : Fin 14) ∈ (C 3 ∩ S03).biUnion id) ((12 : Fin 14) ∈ (C 3 ∩ S23).biUnion id)
  have ht13 := tri_le_one
    ((13 : Fin 14) ∈ (C 1 ∩ S12).biUnion id) ((13 : Fin 14) ∈ (C 1 ∩ S13).biUnion id)
    ((13 : Fin 14) ∈ (C 2 ∩ S12).biUnion id) ((13 : Fin 14) ∈ (C 2 ∩ S23).biUnion id)
    ((13 : Fin 14) ∈ (C 3 ∩ S13).biUnion id) ((13 : Fin 14) ∈ (C 3 ∩ S23).biUnion id)
  have hsumC : ∑ v : Fin 4, ((C v).card : ℤ) =
      (C 0).card + (C 1).card + (C 2).card + (C 3).card := by
    simp [Fin.sum_univ_four]
  have hS_cardZ : (S.card : ℤ) =
      S01.card + S02.card + S03.card + S12.card + S13.card + S23.card := by
    exact_mod_cast hS_card
  rw [hsumC, hS_cardZ]
  dsimp only at hb0 hb1 hb2 hb3
  exact combine_14 hb0 hb1 hb2 hb3 hg01 hg02 hg03 hg12 hg13 hg23 ht6 ht10 ht12 ht13

lemma main_proof :
    ¬ (∃ C : Circuit,
      (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      C.size ≤ 19 ∧
      ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14,
        (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
        Nat.testBit (p.val + 1) v.val) := by
  classical
  rintro ⟨C, hgates, hsize, hcomp⟩
  have hor : ∀ g ∈ C.gates, g.op = GateOp.or := fun g hg => (hgates g hg).1
  have hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hgates g hg).2
  let Wf : Finset (Finset (Fin 14)) := (allSupps C.gates).toFinset
  let S : Finset (Finset (Fin 14)) := Wf.filter isShared
  have hS : ∀ A ∈ S, isShared A := fun A hA => (Finset.mem_filter.mp hA).2
  have hinit_eq : initSupps.toFinset = W0 := by
    ext s
    simp only [initSupps, W0, List.mem_toFinset, List.mem_ofFn, Finset.mem_image,
      Finset.mem_univ, true_and]
  have hW0_init : W0 ⊆ initSupps.toFinset := W0_subset_initSupps
  have hphi := phi_induction C.gates hlen S hS initSupps hW0_init
    (fun X hX hsh => Finset.mem_filter.mpr ⟨hX, hsh⟩)
  have hS_disj : S \ initSupps.toFinset = S := by
    ext X
    simp only [Finset.mem_sdiff, and_iff_left_iff_imp]
    intro hXS hXi
    rw [hinit_eq] at hXi
    simp only [W0, Finset.mem_image, Finset.mem_univ, true_and] at hXi
    obtain ⟨p, rfl⟩ := hXi
    have h2 := (hS {p} hXS).1
    simp at h2
  have hS_sub_Wf : S ⊆ Wf := Finset.filter_subset _ _
  have hS_diff_Wf : S \ Wf = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hS_sub_Wf
  have hWf_union : Wf ∪ S = Wf := Finset.union_eq_left.mpr hS_sub_Wf
  have hM_Wf : M Wf = 0 := by
    unfold M
    apply Finset.sum_eq_zero
    intro v _
    have hW0_Wf : W0 ⊆ Wf := hW0_init.trans (foldl_stepSupp_subset C.gates initSupps)
    have htv : target v ∈ Wf := target_mem_allSupps C hor hcomp v
    rw [coverNum_eq_one v Wf hW0_Wf htv]
    rfl
  have hbound1 : M (W0 ∪ S) + S.card ≤ C.gates.length := by
    change M (initSupps.toFinset ∪ S) + (S \ initSupps.toFinset).card ≤
      M (Wf ∪ S) + (S \ Wf).card + C.gates.length at hphi
    rw [hS_disj, hinit_eq, hWf_union, hM_Wf, hS_diff_Wf, Finset.card_empty] at hphi
    omega
  have hvalid : ∀ A ∈ S, A.card = 3 → ∃ Y ∈ S, Y ⊆ A ∧ Y.card = 2 := by
    intro A hAS hA3
    have hW_card1 : ∀ Z ∈ initSupps.toFinset, Z.card ≤ 1 := by
      intro Z hZ
      rw [hinit_eq] at hZ
      simp only [W0, Finset.mem_image, Finset.mem_univ, true_and] at hZ
      obtain ⟨p, rfl⟩ := hZ
      simp
    obtain ⟨Y, hYWf, hYA, hY2⟩ :=
      shared_triple_has_pair C.gates hlen initSupps hW_card1 A (Finset.mem_filter.mp hAS).1 hA3
    obtain ⟨_, i, j, hij, hi, hj⟩ := hS A hAS
    refine ⟨Y, Finset.mem_filter.mpr ⟨hYWf, ?_⟩, hYA, hY2⟩
    exact ⟨by omega, i, j, hij, hYA.trans hi, hYA.trans hj⟩
  have hCex : ∀ v : Fin 4, ∃ Cv : Finset (Finset (Fin 14)),
      isCover v (W0 ∪ S) Cv ∧ Cv.card = coverNum v (W0 ∪ S) := fun v =>
    exists_min_cover v (W0 ∪ S) Finset.subset_union_left
  choose Cmin hCmin using hCex
  have hcomb := combinatorial_bound S hS hvalid Cmin (fun v => (hCmin v).1)
  have hM_eq : (M (W0 ∪ S) : ℤ) = (∑ v : Fin 4, ((Cmin v).card : ℤ)) - 4 := by
    unfold M
    have hpos : ∀ v : Fin 4, 1 ≤ coverNum v (W0 ∪ S) := fun v =>
      coverNum_pos v (W0 ∪ S) Finset.subset_union_left
    have h0 := hpos 0
    have h1 := hpos 1
    have h2 := hpos 2
    have h3 := hpos 3
    have hc0 := (hCmin 0).2
    have hc1 := (hCmin 1).2
    have hc2 := (hCmin 2).2
    have hc3 := (hCmin 3).2
    simp only [Fin.sum_univ_four]
    omega
  have hsz : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_12408

theorem PEqualNP.Outside.L_meta_12408 :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
      C.size ≤ 19 ∧
      ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14,
        (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
        Nat.testBit (p.val + 1) v.val) :=
  PEqualNP.Outside.L_meta_12408.main_proof

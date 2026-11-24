import YM.Comparison.RG02.Algebra.Nilpotent
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra
import YM.Next.MULTISOURCE.Evaluate
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion

/-!
# Squarefree commuting sources

Coordinate and partition rules in the common marker algebra (no coupling variable here).
No estimates are implicit; in particular evaluation equality does NOT identify two sets of
polymer activities. The conventions below work for varying subsets as long as they are in
one of the allowed modes of the given Census. A part of a partition may carry several
markers. We do not assume symmetry in the physical fields, non-overlapping physical supports,
or distinct field indices. `connected` is interpreted only for normalized inputs.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02

open RG Marker Extra.Trajectories Primitives.GCC.Anchor Multi
open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {R : Census V}

/-- Augmentation homomorphism. -/
def quietMap (R : Census V) : Poly R →ₐ[ℂ] ℂ where
  toFun x := x.part R.quiet
  map_one' := by simp
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := Poly.quiet_mul
  commutes' a := by
    change (Poly.send R.quiet a).part _ = a
    simp

@[simp] theorem quietMap_apply (a : Poly R) : quietMap R a = a.part R.quiet := rfl

/-- Extract one nonempty block; no division by zero-label fields. -/
theorem lit_part_reconstruct (a : Poly R) (h : a.part R.quiet = 0) :
    lit R (fun i => a.part i.val) = a := by
  ext b
  by_cases H : b.val.Nonempty
  · exact part_lit (fun i => a.part i.val) (show Hot R from ⟨b,H⟩)
  · have he : b = R.quiet := Subtype.ext (not_nonempty_iff_eq_empty.mp H)
    rw [he, part_lit_quiet, h]

section
variable [Fintype V]

theorem logTerms_eq (a : Poly R) (h : a.part R.quiet=1) :
    logTerms (Fintype.card V) a = connected a := by
  nth_rw 1 [← pass_connected h]
  change logTerms _ (expTerms _ _) = _
  exact logTerms_expTerms _ (Poly.stops _ (connected_quiet h) _ (Nat.lt_succ_self _))

-- Multiplication by a single formal generator, erasing exactly that occurrence.
omit [Fintype V] in
private theorem mul_fire_part (p : Poly R) (T : R.Mode) (i : V) (x : ℂ) :
    (p * Poly.send (R.fire i) x).part T = if i∈T.val then x *
      p.part (diff T (R.fire i).val) else 0 := by
  rw [mul_comm, mul_at_part]
  simp only [Census.fire, singleton_subset_iff]

/-- Factorial check. No coefficient can survive reuse of the *same* fired marker. -/
theorem lambda_pow_part (a : V → ℂ) (T : R.Mode) (k : ℕ) :
    ((lambda R a)^k).part T =
      if T.val.card = k then (k.factorial:ℂ) * ∏ i∈T.val, a i else 0 := by
  induction k generalizing T with
  | zero =>
    by_cases h : T = R.quiet
    · subst T; simp [Census.quiet]
    · have hc : T.val.card ≠ 0 := fun he => h (Subtype.ext (card_eq_zero.mp he))
      simp [h,hc]
  | succ k ih =>
    have he (i : V) (hi : i∈T.val) : (diff T (R.fire i).val).val = T.val.erase i := by
      simp [diff, Census.fire, sdiff_singleton_eq_erase]
    have term (i : V) (hi : i∈T.val) :
        a i * ((lambda R a)^k).part (diff T (R.fire i).val) =
          if T.val.card=k+1 then (k.factorial:ℂ) * ∏ i∈T.val, a i else 0 := by
      rw [ih, he _ hi, card_erase_of_mem hi]
      have hpos := Finset.card_pos.mpr (show T.val.Nonempty from ⟨i,hi⟩)
      by_cases h : T.val.card = k+1
      · rw [if_pos h, if_pos (by omega), mul_left_comm, mul_prod_erase _ _ hi]
      rw [if_neg h, if_neg (by omega), mul_zero]
    rw [pow_succ]
    nth_rw 2 [lambda]
    rw [Finset.mul_sum, Poly.part_sum]
    simp_rw [mul_fire_part]
    calc
      _ = ∑ i ∈ T.val, a i * ((lambda R a)^k).part (diff T (R.fire i).val) := by
        rw [← Finset.sum_filter]; simp
      _ = ∑ _i ∈ T.val,
          (if T.val.card=k+1 then (k.factorial:ℂ) * ∏ i∈T.val, a i else 0) :=
        sum_congr rfl term
      _ = _ := by
        split <;> rename_i h
        · simp only [sum_const, h, Nat.factorial_succ]
          push_cast
          -- distributing the number of choices of last generator
          simp only [nsmul_eq_mul, Nat.cast_succ]; rw [mul_assoc]
        simp

omit [Fintype V] in
/-- Ordered factors carry a factorial. The `shards` are precisely the unlabelled
partitions of `T`, represented as subfamilies of allowed modes. -/
theorem powers_by_partitions (a : Poly R) (ha : a.part R.quiet=0) (k : ℕ) (T : R.Mode) :
    (a^k).part T = ∑ π∈shards R T,
        if π.val.card=k then (k.factorial:ℂ) * ∏ i∈π.val, a.part i.val else 0 := by
  have he := (substitute_lambda (R:=R) (fun i => a.part i.val)).trans (lit_part_reconstruct a ha)
  have hx : a ^ k = substitute R ((lambda (parts R) fun i => a.part i.val)^k) := by
    rw [map_pow, he]
  rw [hx, substituted]
  simp_rw [lambda_pow_part]

-- The allowed partition arity cannot exceed the number of available markers.
omit [Fintype V] in
private theorem shard_card_le (T : R.Mode) {π : (parts R).Mode} (h : π∈shards R T) :
    π.val.card ≤ T.val.card := by
  rw [← show unionOf π=T from (mem_filter.mp h).2]
  unfold unionOf
  dsimp only
  rw [card_biUnion (parts_wise π)]
  nth_rw 1 [← show ∑ _i∈π.val, 1=π.val.card by simp]
  exact sum_le_sum fun i _ => Finset.card_pos.mpr i.property

/-- Moments on the same set of markers are the partitions of connected weights. -/
theorem pass_partitions (a : Poly R) (ha : a.part R.quiet=0) (T : R.Mode) :
    a.pass.part T = ∑ π ∈ shards R T, ∏ i∈π.val, a.part i.val := by
  unfold Poly.pass
  rw [Poly.part_sum]
  simp_rw [Poly.part_smul, powers_by_partitions _ ha, mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun π hπ => ?_
  rw [sum_eq_single_of_mem π.val.card (mem_range.mpr ?_)]
  · rw [if_pos rfl,inv_mul_cancel_left₀]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  · intro i hi hi'
    rw [if_neg (Ne.symm hi'), mul_zero]
  exact Nat.lt_succ_of_le ((shard_card_le _ hπ).trans (card_le_univ _))

theorem moment_partitions (m : Poly R) (hm : m.part R.quiet=1) (T : R.Mode) :
    m.part T = ∑ π ∈ shards R T, ∏ i∈π.val,(connected m).part i.val := by
  calc
    _ = (Poly.pass (connected m)).part T := by rw [pass_connected hm]
    _ = _ := pass_partitions _ (connected_quiet hm) T

omit [Fintype V] in
private theorem shard_nonempty {T : R.Mode} (h : T.val.Nonempty) {π : (parts R).Mode}
    (hπ : π∈shards R T) : π.val.Nonempty := by
  by_contra! HE
  rw [← show unionOf π=T from (mem_filter.mp hπ).2] at h
  rw [show π = (parts R).quiet from Subtype.ext HE] at h
  simp [Census.quiet,unionOf] at h

/-- Classical (ordinary joint, no complex conjugation) cumulant weight.
Markers are DISTINCT even when the underlying functions on the probability space agree. -/
theorem mobius (m : Poly R) (hm : m.part R.quiet=1) (T : R.Mode) (hT : T.val.Nonempty) :
    (connected m).part T = ∑ π∈shards R T,
      ((-1 : ℂ)^(π.val.card-1) * ((π.val.card-1).factorial:ℂ)) *
        ∏ i∈π.val, m.part i.val := by
  have he : (m-1).part R.quiet=0 := by simp [part_sub,hm]
  rw [← logTerms_eq m hm, logTerms, Poly.part_sum]
  simp_rw [Poly.part_smul, powers_by_partitions _ he, mul_sum]
  rw [Finset.sum_comm]; apply sum_congr rfl
  intro π hπ
  let j := π.val.card-1
  have hc : π.val.card = j+1 := by
    have ht := Finset.card_pos.mpr (shard_nonempty hT hπ)
    dsimp [j]; omega
  have hbound : j < Fintype.card V := by
    have := (shard_card_le _ hπ).trans (card_le_univ _); omega
  rw [sum_eq_single_of_mem j (mem_range.mpr hbound)]
  · rw [if_pos hc]
    have H (i : Hot R) : i.val ≠ R.quiet := by
      intro H; exact i.property.ne_empty (congr_arg Subtype.val H)
    simp only [part_sub,Poly.one_part,if_neg (H _),sub_zero]
    change ((-1:ℂ)^j / _) * _ = ((-1:ℂ)^j * _) * _
    rw [Nat.factorial_succ,Nat.cast_mul, mul_assoc (↑(j+1:ℕ) : ℂ), ← mul_assoc, div_mul_cancel₀]
    · rw [mul_assoc]
    exact_mod_cast Nat.succ_ne_zero j
  intro i hi hi'
  rw [if_neg, mul_zero]; omega

theorem connected_pass {x : Poly R} (hx : x.part R.quiet=0) :
    connected x.pass = x := by
  apply pass_inj (connected_quiet (Poly.pass_part x hx)) hx
  exact pass_connected (Poly.pass_part x hx)

theorem connected_product {x y : Poly R} (hx : x.part R.quiet=1) (hy : y.part R.quiet=1) :
    connected (x*y) = connected x + connected y := by
  rw [show x*y = Poly.pass (connected x + connected y) from ?_,
    connected_pass (by simp only [Poly.part_plus, connected_quiet hx, connected_quiet hy, add_zero])]
  rw [pass_add (connected_quiet hx) (connected_quiet hy), pass_connected hx, pass_connected hy]

/-- Setting some names to zero commutes with connected extraction. -/
theorem connected_maps {V' : Type*} [Fintype V'] [DecidableEq V'] {R' : Census V'}
    (f : Poly R →ₐ[ℂ] Poly R') (hf : ∀ x, (f x).part R'.quiet=x.part R.quiet)
    {x : Poly R} (hx : x.part R.quiet=1) :
    f (connected x) = connected (f x) := by
  apply pass_inj (by rw [hf, connected_quiet hx]) (connected_quiet ((hf x).trans hx))
  rw [← pass_map _ _ (connected_quiet hx) (by rw [hf, connected_quiet hx]),
    pass_connected hx, pass_connected ((hf x).trans hx)]

/-- Split the mode on an arbitrary subset of names. -/
def insideNames (b : Finset V) (p : R.Mode) : R.Mode :=
    ⟨p.val ∩ b, R.down p.property _ inter_subset_left⟩

/-- Projection of the *coefficients*, not restriction of configurations. -/
def onNames (b : Finset V) : Poly R →ₐ[ℂ] Poly R := dilation R (fun i => if i ∈ b then 1 else 0)

omit [Fintype V] in
theorem onNames_part (b : Finset V) (x : Poly R) (i : R.Mode) :
    (onNames b x).part i = if i.val ⊆ b then x.part i else 0 := by
  rw [onNames,dilation_part]
  split <;> rename_i he
  · rw [Finset.prod_eq_one,one_mul]; exact fun j hj => if_pos (he hj)
  have ⟨j,hj,hJ⟩ := not_subset.mp he
  rw [Finset.prod_eq_zero hj (if_neg hJ),zero_mul]

theorem names_split (a : Finset V) (x y : Poly R) (i : R.Mode) :
    (onNames a x * onNames aᶜ y).part i = x.part (insideNames a i)*y.part (insideNames aᶜ i) := by
  let A := insideNames a i
  let B := insideNames aᶜ i
  have hA : A.val ⊆ a := inter_subset_right
  have hB : B.val ⊆ aᶜ := inter_subset_right
  have hm : Poly.merges A B i := by
    refine ⟨Finset.disjoint_left.mpr (fun v hv hv' => Finset.mem_compl.mp (hB hv') (hA hv)),?_⟩
    simp [A,B,insideNames,← Finset.inter_union_distrib_left]
  have he (u v : R.Mode) (hU : u.val ⊆ a) (hV : v.val ⊆ aᶜ)
      (h : Poly.merges u v i) : u=A ∧ v=B := by
    have hu : u=A := by
      apply Subtype.ext
      ext j
      change j ∈ u.val ↔ j ∈ i.val ∩ a
      rw [mem_inter, ← h.2,mem_union]
      constructor
      · intro H; exact ⟨Or.inl H, hU H⟩
      rintro ⟨H,K⟩; exact H.resolve_right (fun J => mem_compl.mp (hV J) K)
    exact ⟨hu,(separates_unique _ _ _ h).trans (by rw [hu, (separates_unique _ _ _ hm).symm])⟩
  rw [Poly.part_mul, Finset.sum_eq_single_of_mem A (mem_univ A)]; rotate_left
  · intro j hj hj'
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [onNames_part, onNames_part]
    split_ifs with hz hu hv
    · exact False.elim (hj' (he j k hu hv hz).1)
    all_goals simp
  rw [Finset.sum_eq_single_of_mem B (mem_univ B)]
  · rw [if_pos hm,onNames_part,onNames_part,if_pos hA,if_pos hB]
  intro j hj hj'
  rw [onNames_part,if_pos hA,onNames_part]
  split_ifs with hu hv
  · exact False.elim (hj' (he A j hA hv hu).2)
  all_goals simp

/-- Factorization on either side of a cut only up to a subset `t`. All cross terms
through `t` in the full log disappear. E.g. this can be applied to a fixed graph choice
in which weights are set to zero on subsets that split a required pair. -/
theorem cumulant_cancellation (a : Finset V) (m : Poly R) (hm : m.part R.quiet=1)
    (t : Finset V) (factor : ∀ j : R.Mode, j.val ⊆ t →
        m.part j = m.part (insideNames a j)*m.part (insideNames aᶜ j))
    (i : R.Mode) (hi : i.val ⊆ t) (hl : ¬ i.val ⊆ a) (hr : ¬ i.val ⊆ aᶜ) :
    (connected m).part i = 0 := by
  have he : UpTo t m (onNames a m * onNames aᶜ m) := by
    intro j hj; rw [names_split]; exact factor j hj
  have hk (b : Finset V) (x : Poly R) : (onNames b x).part R.quiet=x.part R.quiet := by
    rw [onNames_part, if_pos (show R.quiet.val ⊆ b from empty_subset _)]
  rw [he.conn i hi, connected_product ((hk _ _).trans hm) ((hk _ _).trans hm),
    ← connected_maps _ (hk a) hm, ← connected_maps _ (hk aᶜ) hm,
    Poly.part_plus, onNames_part, if_neg hl, onNames_part, if_neg hr, zero_add]

end

end YM.Comparison.RG02

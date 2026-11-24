import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra
import YM.Next.MULTISOURCE.Evaluate

/-!
# Joint cumulants on an admitted list

Enhance `Extra.Trajectories.connected` and `Primitives.GCC.Anchor` with partition
interfaces. In particular: exact counts with the `YM.Multi.parts` Census from the polarized
multi-source calculation. Use occurrences as names, even if some read the same observable. **No
assumption that multiplying sources means independent measurements**. `highlight` uses one
root, and is legitimate on the square-free product (in contrast to ordinary formal ∂ itself).
-/
set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02.Cumulants
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected pass_inj pass_add pass_zero
  part_sub)
open Finset
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V] {R : Census V}

lemma hot_iff_ne (s : R.Mode) : s.val.Nonempty ↔ s ≠ R.quiet :=
  by simp only [ne_eq, Subtype.ext_iff]; exact nonempty_iff_ne_empty

lemma lit_identity (x : Poly R) (hx : x.part R.quiet = 0) :
    lit R (fun i => x.part i.val) = x := by
  ext i
  by_cases h : i.val.Nonempty
  · exact part_lit (fun j => x.part j.val) ⟨i, h⟩
  · replace h := of_not_not (mt (hot_iff_ne i).2 h)
    rw [h,hx,part_lit_quiet]

section Highlight
/-- Multiply by one on the terms containing marker i, zero on the others. Euler derivative
in one marker descends to the quotient (and treats coupler markers the same as all the others).
`R.down` needed for all the usual products. -/
def highlight (i : V) : Poly R →ₗ[ℂ] Poly R where
  toFun x := usingAll {i} x
  map_add' := by
    intro x y; ext s; change (if _ then x.part s + y.part s else 0) =
      (if _ then x.part s else 0) + (if _ then y.part s else 0)
    split <;> simp [*]
  map_smul' := by
    intro c x; ext s; change (if _ then c * x.part s else 0) =
      c * (if _ then x.part s else 0)
    split <;> simp [*]

lemma highlight_part (i : V) (x : Poly R) (s) :
    (highlight i x).part s = if i ∈ s.val then x.part s else 0 := by
  change (if {i} ⊆ s.val then _ else 0) = _; simp only [singleton_subset_iff]

lemma highlight_send (i : V) (s : R.Mode) (a : ℂ) : highlight i (Poly.send s a) =
    if i ∈ s.val then Poly.send s a else 0 := by
  ext t; rw [highlight_part, Poly.part_send]; by_cases h : t=s <;> subst_vars <;>
    split_ifs <;> simp_all

@[simp] lemma highlight_quiet (i : V) (x : Poly R) : (highlight i x).part R.quiet = 0 := by
  simp [highlight_part, Census.quiet]

lemma highlight_mul (i : V) (x y : Poly R) : highlight i (x*y) = highlight i x*y+x*highlight i y := by
  have H (s t : R.Mode) (a b : ℂ) : highlight i (Poly.send s a * Poly.send t b) =
      highlight i (Poly.send s a)*Poly.send t b + Poly.send s a * highlight i (Poly.send t b) := by
    by_cases h : ∃ w, Poly.merges s t w
    · obtain ⟨w,h⟩ := h
      have hw : i∈w.val ↔ i∈s.val ∨ i∈t.val := h.2 ▸ mem_union
      have hd (he : i∈s.val) : i∉t.val := fun ht => disjoint_left.mp h.1 he ht
      rw [send_prod h]; by_cases hs : i∈s.val
      · simp [hw, hs, hd hs, highlight_send, send_prod h]
      by_cases ht : i∈t.val <;> simp [hw, hs, ht, highlight_send, send_prod h]
    rw [send_noProd h, map_zero, highlight_send, highlight_send]
    split_ifs <;> simp [send_noProd h]
  rw [← Poly.studs x, ← Poly.studs y]
  simp_rw [sum_mul,mul_sum,map_sum,H,sum_add_distrib]
  -- distribute nested
  simp_rw [mul_sum, sum_mul]
  exact congrArg (· + _) (sum_comm (f:=fun s t => highlight i (Poly.send s (x.part s)) * Poly.send t (y.part t)))

@[simp] lemma highlight_one (i : V) : highlight i (1 : Poly R) = 0 := by
  change highlight i (Poly.send _ _) = _; simp [highlight_send, Census.quiet]

lemma highlight_pow (i : V) (x : Poly R) (n : ℕ) :
    highlight i (x^(n+1)) = ((↑(n+1) : ℂ)) • (x^n * highlight i x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ _ (n+1), highlight_mul, ih, smul_mul_assoc]
    push_cast
    rw [pow_succ]; rw [show x ^ n * highlight i x * x = x ^ n * x * highlight i x by ring]
    simp only [add_smul, one_smul]

end Highlight

section Logarithm
variable [Fintype V]

lemma connected_pass {a : Poly R} (h : a.part R.quiet = 0) : connected (Poly.pass a) = a :=
  pass_inj (connected_quiet (Poly.pass_part a h)) h (pass_connected (Poly.pass_part a h))

lemma connected_mul {x y : Poly R} (hx : x.part R.quiet=1) (hy : y.part R.quiet=1) :
    connected (x*y) = connected x + connected y := by
  have h (z : Poly R) (hz : z.part R.quiet=1) := connected_quiet hz
  apply pass_inj (h (x*y) (by simp [hx,hy])) (by simp [h _ hx,h _ hy]);
  rw [pass_add (h x hx) (h y hy), pass_connected hx, pass_connected hy,
    pass_connected (show (x*y).part R.quiet=1 from by simp [hx,hy])]

lemma highlight_pass (i : V) (x : Poly R) (hx : x.part R.quiet=0) :
    highlight i (Poly.pass x) = Poly.pass x * highlight i x := by
  let n := Fintype.card V
  have htail : x^n * highlight i x = 0 := final_vanish x _ hx (highlight_quiet i _)
  unfold Poly.pass
  rw [map_sum, sum_range_succ', sum_mul, sum_range_succ _ (Fintype.card V)]
  rw [smul_mul_assoc, show x^Fintype.card V * highlight i x = 0 from htail]
  simp only [map_smul, pow_zero, highlight_one, smul_zero, add_zero, highlight_pow, smul_smul,
    smul_mul_assoc]; refine sum_congr rfl fun j _=> ?_
  have he : ((↑(j+1) : ℂ)) ≠ 0 := by exact_mod_cast j.succ_ne_zero
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ he, mul_one]

lemma moment_root (i : V) (m : Poly R) (hm : m.part R.quiet=1) :
    highlight i m = m * highlight i (connected m) := by
  simpa only [pass_connected hm] using highlight_pass i (connected m) (connected_quiet hm)

lemma connected_root (i : V) (m : Poly R) (hm : m.part R.quiet=1) :
    highlight i (connected m) = highlight i m * inverseMass m := by
  calc
    _ = m * inverseMass m * highlight i (connected m) := by rw [right_inverse hm, one_mul]
    _ = highlight i m * inverseMass m := by rw [moment_root i m hm]; ring

lemma geometric_inverse (x : Poly R) (hx : x.part R.quiet=1) :
    inverseMass x = ∑ n ∈ range (Fintype.card V + 1), (1-x)^n := by
  let y := 1-x; have h : x=1-y := by unfold y; abel
  let z := ∑ n ∈ range (Fintype.card V + 1), y^n
  have hx' : x*z=1 := by
    unfold z; nth_rw 1 [h]; rw [mul_neg_geom_sum]
    rw [Poly.stops y (by simp [y,hx,part_sub]) _ (by omega), sub_zero]
  change inverseMass x=z
  calc
    _ = (x*z)*inverseMass x := by rw [hx', one_mul]
    _ = x*inverseMass x *z := by ring
    _ = _ := by rw [right_inverse hx, one_mul]

/-- The usual finite logarithm, written with powers of 1-x to simplify signs.
    The last (power = `Fintype.card V+1`) term is null on nominal input. -/
def unipotentLog (x : Poly R) :=
  ∑ n ∈ range (Fintype.card V + 1), (-((↑(n+1) : ℂ))⁻¹) • (1-x)^(n+1)

lemma log_quiet {x : Poly R} (hx : x.part R.quiet=1) :
    (unipotentLog x).part R.quiet = 0 := by
  unfold unipotentLog
  simp [Poly.part_sum, pow_succ, part_sub, hx]

lemma log_highlight {x : Poly R} (hx : x.part R.quiet=1) (i : V) :
    highlight i (unipotentLog x) = highlight i x * inverseMass x := by
  unfold unipotentLog
  rw [map_sum, geometric_inverse x hx, mul_sum]; apply sum_congr rfl; intro n hn
  have ht : (↑(n+1) : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [map_smul, highlight_pow, map_sub, highlight_one, zero_sub,
    smul_smul, neg_mul, inv_mul_cancel₀ ht]
  simp [mul_comm]

lemma log_formula {x : Poly R} (hx : x.part R.quiet=1) : connected x = unipotentLog x := by
  ext s; by_cases h : s.val.Nonempty
  · obtain ⟨i,hi⟩ := h
    simpa [highlight_part,hi] using congrArg (Poly.part · s)
      ((connected_root i x hx).trans (log_highlight hx i).symm)
  replace h := of_not_not (mt (hot_iff_ne s).2 h)
  rw [h, connected_quiet hx, log_quiet hx]

end Logarithm

section Lambda
variable [Fintype V] (f : V → ℂ)

lemma highlight_lambda (i : V) : highlight i (lambda R f) = Poly.send (R.fire i) (f i) := by
  simp only [lambda,map_sum,highlight_send,Census.fire,mem_singleton]
  simp

omit [Fintype V] in
lemma mul_fire_part (i : V) (t : R.Mode) (h : i∈t.val) (a : ℂ) (x : Poly R) :
    (Poly.send (R.fire i) a * x).part t = a*x.part (diff t {i}) := by
  rw [mul_at_part]; simp only [Census.fire,singleton_subset_iff,h,↓reduceIte]

/-- Polarization factorial. Uses distinct occurrences only. -/
lemma factorial_lambda (n : ℕ) (s : R.Mode) : (lambda R f ^ n).part s =
    if s.val.card = n then (n.factorial:ℂ) * ∏ i∈s.val, f i else 0 := by
  classical
  induction n generalizing s with
  | zero =>
    -- lambda power 0
    rw [pow_zero, Poly.one_part]; split_ifs with h h' h'
    · subst s; simp [Census.quiet]
    · simp [Census.quiet,h] at h'
    replace h' := card_eq_zero.mp h'; exact False.elim (h (Subtype.ext h'))
    rfl
  | succ n ih =>
    by_cases h : s.val.Nonempty; swap
    · have he := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)
      rw [Poly.high _ (lambda_quiet f) _ s (by omega), he, if_neg (by omega)]
    obtain ⟨i,hi⟩ := h
    have hz : (diff (R:=R) s {i}).val = s.val.erase i := sdiff_singleton_eq_erase ..
    rw [← (show (highlight i (lambda R f ^ (n+1))).part s=_ from
      (highlight_part i _ _).trans (if_pos hi)), highlight_pow,highlight_lambda,
      Poly.part_smul,mul_comm (lambda R f ^ n),mul_fire_part i s hi, ih]
    simp only [hz]
    rw [card_erase_of_mem hi,← mul_prod_erase _ f hi]; have he := card_pos.mpr ⟨_,hi⟩
    split_ifs with h h' h' <;> first | omega | (rw [Nat.factorial_succ]; push_cast; ring) | simp

lemma pass_lambda (s : R.Mode) : (Poly.pass (lambda R f)).part s = ∏ i∈s.val, f i := by
  unfold Poly.pass; rw [Poly.part_sum]; simp_rw [Poly.part_smul, factorial_lambda]
  rw [sum_eq_single s.val.card]
  · have h: (s.val.card.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos s.val.card).ne'
    simp [h]
  · intro i _ hi; rw [if_neg hi.symm,mul_zero]
  intro h; exact False.elim (h (mem_range.mpr (Nat.lt_succ_of_le (card_le_univ _))))

/-- Cumulant partition sign/multiplicity. Convention: number of NONEMPTY blocks,
    `log(1+input)`; never charge ordering permutations again. -/
def mobiusTop (d : ℕ) : ℂ := if d=0 then 0 else (-1)^(d-1) * ↑(d-1).factorial

lemma part_one_plus_lambda_inv (t : R.Mode) :
    (inverseMass (1+lambda R f)).part t = (-1)^t.val.card * (t.val.card.factorial:ℂ) *
      ∏ i∈t.val, f i := by
  rw [geometric_inverse _ (by simp [lambda_quiet f]),Poly.part_sum]
  have hv : (-lambda R f) = lambda R (-f) := by
    simp only [lambda, Pi.neg_apply, ← Finset.sum_neg_distrib]
    congr 1
    funext i; ext j; by_cases h : j=R.fire i <;> simp [h]
  simp_rw [sub_add_eq_sub_sub, sub_self, zero_sub, hv,factorial_lambda]
  rw [sum_eq_single t.val.card]
  · simp [prod_neg]; ring
  · intro i _ hi; rw [if_neg hi.symm]
  intro h; exact False.elim (h (mem_range.mpr (Nat.lt_succ_of_le (card_le_univ _))))

lemma log_lambda (t : R.Mode) :
    (connected (1+lambda R f)).part t = mobiusTop t.val.card * ∏ i∈t.val, f i := by
  have h : (1+lambda R f).part R.quiet=1 := by simp [lambda_quiet _]
  by_cases hi : t.val.Nonempty
  · obtain ⟨i,hi⟩ := hi
    rw [← (show (highlight i (connected _)).part t = _ from
        (highlight_part i (connected (1+lambda R f)) t).trans (if_pos hi)),
      connected_root i _ h, map_add, highlight_one, zero_add, highlight_lambda,
      mul_fire_part _ t hi, part_one_plus_lambda_inv]
    have he : t.val.card ≠ 0 := (card_pos.mpr ⟨_,hi⟩).ne'
    unfold mobiusTop; rw [if_neg he, (show (diff t {i}).val = t.val.erase i from sdiff_singleton_eq_erase ..),
      card_erase_of_mem hi, ← mul_prod_erase _ f hi]; ring
  · rw [of_not_not (mt (hot_iff_ne t).2 hi), connected_quiet h]; simp [mobiusTop,Census.quiet]

end Lambda

section Shards
variable [Fintype V]

omit [Fintype V] in
lemma substitute_quiet (x : Poly (parts R)) :
    (substitute R x).part R.quiet = x.part (parts R).quiet := by
  rw [substituted]; unfold shards; simp only [Finset.sum_filter]; rw [Finset.sum_eq_single (parts R).quiet]
  · simp
  · intro t _ ht; rw [if_neg]; intro h
    obtain ⟨i,hi⟩ := (hot_iff_ne t).2 ht
    obtain ⟨v,hv⟩ := i.property
    have hp : v∈(unionOf t).val := mem_biUnion.mpr ⟨_,hi,hv⟩
    rw [h] at hp; exact notMem_empty _ hp
  simp

lemma pass_partition (x : Poly R) (h : x.part R.quiet=0) (t : R.Mode) :
    (Poly.pass x).part t = ∑ s∈shards R t,∏ i∈s.val,x.part i.val := by
  let f (i : Hot R) := x.part i.val
  have he : (substitute R) (lambda _ f) = x := (substitute_lambda f).trans (lit_identity x h)
  nth_rw 1 [← he]
  simp_rw [← pass_map (substitute R) _ (lambda_quiet f) (by rw [he,h]), substituted, pass_lambda]; rfl

/-- Transmit exact logarithm through *algebra* maps preserving the quiet part. Thus we can use
Euler/cumulant rules with extra bookkeeping variables, substitute, and collect coefficients.
An overlapping conflict is zero in the target algebra (use admission-respecting maps).
`hF` makes the augmentation bookkeeping explicit. -/
lemma log_map {W : Type*} [DecidableEq W] [Fintype W] {S : Census W}
    (F : Poly R →ₐ[ℂ] Poly S) (hF : ∀ x : Poly R,(F x).part S.quiet = x.part R.quiet)
    {x : Poly R} (hx : x.part R.quiet = 1) : F (connected x)=connected (F x) := by
  have h := (hF x).trans hx
  refine pass_inj ((hF _).trans (connected_quiet hx)) (connected_quiet h) ?_
  rw [← pass_map F _ (connected_quiet hx) ( (hF _).trans (connected_quiet hx)), pass_connected h,
    pass_connected hx]

/-- The actual partition formula for *any* input x with quiet part 1. This includes
ordinary moments using the shared predictor tags/conditional normalizer, as well as
moments over the full flat Gaussian used for the independent coefficients. -/
lemma log_partition (x : Poly R) (h : x.part R.quiet=1) (t : R.Mode) :
    (connected x).part t = ∑ s∈shards R t,mobiusTop s.val.card * ∏ i∈s.val,x.part i.val := by
  let a : Hot R → ℂ := fun i => x.part i.val
  have he (i : Hot R) : (x-1).part i.val = a i := by
    simp [a, part_sub, (hot_iff_ne _).1 i.property]
  have hm : (substitute R) (1+lambda _ a) = x := by
    rw [map_add, map_one, substitute_lambda, ← funext he,
      lit_identity (x-1) (by simp [part_sub,h]), add_sub_cancel]
  nth_rw 1 [← hm]
  simp_rw [← log_map (substitute R) substitute_quiet (show (1+lambda (parts R) a).part (parts R).quiet = 1 from by simp [lambda_quiet _]), substituted,
    log_lambda]
  rfl

end Shards
end YM.Comparison.RG02.Cumulants

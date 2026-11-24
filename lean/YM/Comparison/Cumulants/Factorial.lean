import YM.Comparison.Cumulants.Bell

/-!
# Finite logarithm and precise factorials

Alternative *formulas* for the very same `connected`.
`log_partition_formula`: primitive log coefficient at an allowed set of names.
Counts factors even of identical numerical value at the same physical/root location.
Includes all partitions, before any diagrammatic connected cancellation.
There is an outer parameter in the later application; that application performs
all these operations on a single normalized moment functional, *not* tag-wise.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Cumulants

open Finset Function Marker Multi Extra.Trajectories Primitives.GCC
open scoped BigOperators

variable {V : Type} [DecidableEq V] {R : Census V}

/-- Multiplicity/marker Euler derivation (unlike repeated ordinary derivatives
in one square-zero name, it's a derivation on the existing truncated algebra). -/
def loads (R : Census V) : Poly R →ₗ[ℂ] Poly R where
  toFun x := Poly.inject fun s => (s.val.card:ℂ) * x.part s
  map_add' x y := by
    ext i; exact mul_add _ _ _
  map_smul' z x := by
    ext i; exact mul_left_comm (i.val.card:ℂ) z (x.part i)

lemma loads_part (x : Poly R) (s) : ((loads R) x).part s = (s.val.card:ℂ) * x.part s := rfl
lemma loads_quiet (x : Poly R) : (loads R x).part R.quiet = 0 := by rw [loads_part]; simp [Census.quiet]

lemma loads_mul (x y : Poly R) : loads R (x*y) = loads R x*y+x*loads R y := by
  ext i
  simp_rw [loads_part, Poly.part_plus, Poly.part_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
  split
  next he =>
    rw [← he.2,card_union_of_disjoint he.1, Nat.cast_add,loads_part,loads_part]; ring
  simp only [mul_zero,add_zero]

lemma loads_one : loads R 1 = 0 := by
  ext i
  by_cases hi : i=R.quiet
  · subst i; rw [loads_quiet,Poly.part_nil]
  rw [loads_part,Poly.one_part, if_neg hi, mul_zero,Poly.part_nil]

lemma loads_power (x : Poly R) (k : ℕ) :
    loads R (x^(k+1)) = (↑(k+1:ℕ):ℂ) • (x^k * loads R x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, loads_mul, ih, smul_mul_assoc,
      show x^k * loads R x * x = x^(k+1)*loads R x by ring, Nat.cast_add_one (k+1), add_smul,one_smul]

lemma loads_injective {x y : Poly R} (hx : x.part R.quiet = y.part R.quiet)
    (h : loads R x = loads R y) : x=y := by
  ext i
  by_cases hi : i.val.Nonempty
  · exact mul_left_cancel₀ (a:=(i.val.card:ℂ)) (Nat.cast_ne_zero.mpr (card_pos.mpr hi).ne')
      (congrArg (fun z => (z : Poly R).part i) h)
  rw [eq_quiet_of_empty i hi,hx]

variable [Fintype V]

lemma loads_pass (x : Poly R) (hx : x.part R.quiet=0) :
    loads R x.pass = x.pass * loads R x := by
  let L := Fintype.card V
  unfold Poly.pass; rw [map_sum, sum_range_succ' _ L, sum_mul, sum_range_succ _ L]
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,loads_one,add_zero,
    smul_mul_assoc,final_vanish x (loads R x) hx (loads_quiet x), smul_zero,add_zero]
  refine sum_congr rfl fun i _ => ?_
  have h : ((↑(i+1).factorial:ℂ)⁻¹) * (↑(i+1:ℕ):ℂ) = (↑(i.factorial):ℂ)⁻¹ := by
    rw [Nat.factorial_succ,Nat.cast_mul,mul_inv_rev,mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)), mul_one]
  rw [map_smul, loads_power, smul_smul,h, smul_mul_assoc]

lemma connected_euler {x : Poly R} (h : x.part R.quiet=1) :
    x * loads R (connected x) = loads R x := by
  have ht := loads_pass _ (connected_quiet h); rw [pass_connected h] at ht; exact ht.symm

/-- Evaluate the polynomial log series on `1+x`. -/
def formalLog (x : Poly R) : Poly R :=
  ∑ k∈Finset.range (Fintype.card V), ((-1:ℂ)^k / (↑(k+1:ℕ):ℂ)) • x^(k+1)

lemma log_series_euler (x : Poly R) (h : x.part R.quiet = 0) :
    (1+x)*loads R (formalLog x) = loads R x := by
  let L := Fintype.card V
  let Y (n) := ∑ k∈Finset.range n,
    ((-1:ℂ)^k / (↑(k+1:ℕ):ℂ)) • x^(k+1)
  let c (i : ℕ) : Poly R := ((-1:ℂ)^i) • (x^i * loads R x)
  have hd (n) : (1+x)*loads R (Y n) = loads R x - c n := by
    induction n with
    | zero => simp [Y,c]
    | succ n ih =>
      rw [show Y (n+1)=Y n + _ from sum_range_succ .., map_add, mul_add, ih]
      rw [map_smul,loads_power, smul_smul, div_mul_cancel₀ _
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)), add_mul, one_mul,
        show x*(((-1:ℂ)^n) • (x^n * loads R x)) = - c (n+1) by
          unfold c
          rw [pow_succ, show (-1:ℂ)^n * -1 = -((-1:ℂ)^n) by ring, neg_smul, neg_neg,mul_smul_comm,
            show x*(x^n*loads R x) = x^(n+1)*loads R x by ring]]
      change loads R x - c n + (c n + -c (n+1))=_; abel
  have he := hd L
  dsimp only [Y,c,L] at he
  rwa [final_vanish _ _ h (loads_quiet _), smul_zero,sub_zero] at he

lemma log_series_quiet (x : Poly R) (h : x.part R.quiet=0) :
    (formalLog x).part R.quiet=0 := by
  unfold formalLog; rw [Poly.part_sum]; refine sum_eq_zero fun i _ => ?_
  rw [Poly.part_smul, pow_succ,Poly.quiet_mul,h,mul_zero,mul_zero]

lemma log_series_companion (x : Poly R) (h : x.part R.quiet=0) :
    connected (1+x)=formalLog x := by
  have he : (1+x).part R.quiet=1 := by simp [h]
  refine loads_injective ((connected_quiet he).trans (log_series_quiet x h).symm) ?_
  let q := Anchor.inverseMass (1+x)
  have hr : q * (1+x)=1 := (mul_comm ..).trans (Anchor.right_inverse he)
  have ht : (1+x)*loads R (connected (1+x))=(1+x)*loads R (formalLog x) := by
    rw [connected_euler he,map_add, loads_one,zero_add,log_series_euler x h]
  exact calc
    _ = 1*loads R (connected (1+x)) := (one_mul _).symm
    _ = 1*loads R (formalLog x) := by
      conv_lhs => lhs; rw [← hr]
      conv_rhs => lhs; rw [← hr]
      rw [mul_assoc, mul_assoc, ht]
    _ = _ := one_mul _

lemma log_series_formula {x : Poly R} (h : x.part R.quiet=1) :
    connected x=formalLog (x-1) := by
  have hh := log_series_companion (x-1) (by rw [part_sub,h]; simp)
  rwa [show 1+(x-1) = x by abel] at hh

/-- The Euler derivation diagonalizes the computation with only singleton markers. -/
lemma lambda_degree (a : V→ℂ) : loads R (lambda R a)=lambda R a := by
  unfold lambda; rw [map_sum]; refine sum_congr rfl fun i _ => ?_
  ext s
  by_cases hs : s=R.fire i
  · subst s; simp [loads_part,Census.fire]
  rw [loads_part,Poly.part_send,if_neg hs,mul_zero]

lemma lambda_degree_pow (a : V→ℂ) (k : ℕ) :
    loads R ((lambda R a)^k) = (k:ℂ) • (lambda R a)^k := by
  cases k with
  | zero => simp only [pow_zero,loads_one,Nat.cast_zero, zero_smul]
  | succ k => rw [loads_power, lambda_degree, ← pow_succ]

lemma lambda_pow_mismatch (a : V → ℂ) (k : ℕ) (t : R.Mode) (h : t.val.card ≠ k) :
    ((lambda R a)^k).part t=0 := by
  have he := congrArg (fun z : Poly R => z.part t) (lambda_degree_pow (R:=R) a k)
  change (↑(t.val.card):ℂ)*_=(k:ℂ)*_ at he
  exact (mul_eq_zero.mp (show ((↑(t.val.card):ℂ)-(k:ℂ))*((lambda R a)^k).part t=0 by
    rw [sub_mul,sub_eq_zero]; exact he)).resolve_left (sub_ne_zero.mpr (by exact_mod_cast h))

/-- All factorials in the occurrence convention come from powers and
exponential/log Taylor coefficients, not part extraction. -/
lemma lambda_power (a : V→ℂ) (k : ℕ) (t : R.Mode) :
    ((lambda R a)^k).part t = if k=t.val.card then (k.factorial:ℂ)*(∏ i∈t.val,a i) else 0 := by
  split_ifs with hk
  · have he : (Poly.pass (lambda R a)).part t = ∏ i∈t.val,a i := pass_fire a t
    unfold Poly.pass at he; rw [Poly.part_sum,sum_eq_single k] at he
    · rw [← he, Poly.part_smul, ← mul_assoc,mul_inv_cancel₀ (show (k.factorial:ℂ) ≠ 0 from
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),one_mul]
    · intro i _ hi; rw [Poly.part_smul,lambda_pow_mismatch a i t (by omega),mul_zero]
    intro h; have he : k ≤ _ := hk ▸ t.val.card_le_univ
    simp [Nat.lt_succ_of_le he] at h
  exact lambda_pow_mismatch a k t (Ne.symm hk)

private lemma rawSingle (a : V→ℂ) (t : R.Mode) :
    (connected (1+lambda R a)).part t =
      if t.val.card=0 then 0 else
        (-1:ℂ)^(t.val.card-1) * ((t.val.card-1).factorial:ℂ) * ∏ i∈t.val,a i := by
  have he := lambda_quiet (R:=R) a
  rw [log_series_companion _ he,formalLog,Poly.part_sum]
  rcases hk : Finset.card t.val with _|k
  · simp only [if_true]
    refine sum_eq_zero fun i _ => ?_
    simp [Poly.part_smul,lambda_power,hk]
  · rw [if_neg (by omega)]
    rw [Finset.sum_eq_single k]
    · rw [Poly.part_smul,lambda_power, if_pos (by omega),Nat.factorial_succ,Nat.cast_mul,
        show k+1-1=k by omega]
      have h : (↑(k+1:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      field_simp
    · intro i _ hi; rw [Poly.part_smul,lambda_power, if_neg (by omega),mul_zero]
    intro h; exfalso
    have hv := t.val.card_le_univ; simp at h; omega

/-- Partition-lattice log coefficient. If `t` is quiet the log coefficient is zero,
including when it is the only mode. Unordered Bell partitions; no unjustified
connectedness criterion under a tag average is baked into this formula. -/
theorem log_partition_formula {a : Poly R} (h : a.part R.quiet=1) (t : R.Mode) :
    (connected a).part t =
      ∑ q∈shards R t, if q.val.card=0 then 0 else
        (-1:ℂ)^(q.val.card-1) * ((q.val.card-1).factorial:ℂ) * ∏ i∈q.val,a.part i.val := by
  let F := fun i : Multi.Hot R => a.part i.val
  have hq : substitute R (1+lambda (parts R) F) = a := by
    rw [map_add,map_one,substitute_lambda]
    have hh : lit R F=a-1 := by
      rw [← lit_expansion (a-1) (by rw [part_sub,h]; simp)]
      apply congrArg (lit R); funext i
      have hx : i.val ≠ R.quiet := fun e => i.property.ne_empty (congrArg Subtype.val e)
      rw [part_sub, Poly.one_part, if_neg hx,sub_zero]
    rw [hh]; abel
  nth_rw 1 [← hq]
  rw [connected_map _ substitute_quiet (show (1+lambda (parts R) F).part (parts R).quiet=1 by
    simp [lambda_quiet]), substituted]
  exact sum_congr rfl fun i _ => rawSingle F i

omit [Fintype V] in
/-- A version of the power count also with mixed vertices in the exponent. -/
lemma augmented_power (x : Poly R) (h : x.part R.quiet=0) (t : R.Mode) (k : ℕ) :
    (x^k).part t =
      ∑ q∈shards R t, if k=q.val.card then (k.factorial:ℂ)*(∏ i∈q.val,x.part i.val) else 0 := by
  let f := lambda (parts R) (fun i : Multi.Hot R => x.part i.val)
  have hh : substitute R f=x := by unfold f; rw [substitute_lambda,lit_expansion _ h]
  rw [show x^k=substitute R (f^k) by rw [map_pow,hh],substituted]
  exact sum_congr rfl fun i _ => lambda_power _ _ _
end YM.Comparison.Cumulants

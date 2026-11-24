import YM.RG02.Marker.Euler
import YM.Next.MULTISOURCE.Shards
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-!
# Partition/factorial formula on the physical census

Use the existing unordered partitions `YM.Multi.shards`. The formulas
include the case where the census omits some higher products. Equal entries
of a table (same mark on different factors, same underlying field evaluated
in several Markov terms, etc.) must still use these partitions; don't cross
a slot with itself, and don't divide again by a permutation factorial when
two *different* slots read the same physical field.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Marks

open Marker Multi Extra.Trajectories Finset
open scoped BigOperators
variable {ι : Type} [DecidableEq ι] {R : Census ι}

theorem lit_parts {x : Poly R} (hx : x.part R.quiet = 0) :
    lit R (fun i => x.part i.val) = x := by
  ext s
  by_cases he : s = R.quiet
  · subst s; rw [part_lit_quiet,hx]
  let z : Multi.Hot R := ⟨s, nonempty_iff_ne_empty.mpr fun h => he (Subtype.ext h)⟩
  exact part_lit (fun i => x.part i.val) z

section Fin
variable [Fintype ι]

theorem pass_partition {x : Poly R} (hx : x.part R.quiet = 0) (s : R.Mode) :
    (Poly.pass x).part s = ∑ p∈shards R s, ∏ b∈p.val,x.part b.val := by
  let y := Multi.lambda (parts R) (fun i => x.part i.val)
  have h : Multi.substitute R y = x := (substitute_lambda ..).trans (lit_parts hx)
  nth_rw 1 [← h]
  have hy : y.part (parts R).quiet=0 := lambda_quiet ..
  rw [← pass_map _ _ hy (h ▸ hx),substituted]
  exact sum_congr rfl fun p _ => pass_fire (R:=parts R) (fun i => x.part i.val) p

theorem from_connected {x : Poly R} (hx : x.part R.quiet=1) (s : R.Mode) :
    x.part s = ∑ p∈shards R s, ∏ i∈p.val,(connected x).part i.val := by
  nth_rw 1 [← pass_connected hx]
  exact pass_partition (connected_quiet hx) _

/-- Coefficient of k numbered marked factors; `x^k/k!`. Includes k=0 or
`s` empty. The formula follows without selecting orderings, by varying
one fugacity then using polynomial identity. -/
theorem number_factors {x : Poly R} (hx : x.part R.quiet = 0) (s : R.Mode) (k : ℕ) :
    (k.factorial:ℂ)⁻¹ * (x^k).part s =
      ∑ p∈(shards R s).filter (fun i => i.val.card=k), ∏ b∈p.val,x.part b.val := by
  let N := max k (Fintype.card ι)
  let w (i : ℕ) := (i.factorial:ℂ)⁻¹ * (x^i).part s
  let a := ∑ i∈range (N+1), Polynomial.monomial i (w i)
  let W (p : (parts R).Mode) := ∏ b∈p.val,x.part b.val
  let b := ∑ p∈shards R s, Polynomial.monomial p.val.card (W p)
  have he : a=b := by
    apply Polynomial.funext
    intro r
    have hr : (r • x).part R.quiet=0 := by simp [hx]
    have hl : a.eval r = (Poly.pass (r • x)).part s := by
      rw [pass_extended _ hr (le_max_right ..), Poly.part_sum]
      unfold a
      rw [Polynomial.eval_finsetSum]
      apply sum_congr rfl
      intro i _; rw [Polynomial.eval_monomial, smul_pow,Poly.part_smul,Poly.part_smul]; unfold w; ring
    rw [hl,pass_partition hr]
    unfold b
    rw [Polynomial.eval_finsetSum]
    apply sum_congr rfl
    intro p _; rw [Polynomial.eval_monomial]
    unfold W; simp_rw [Poly.part_smul]; rw [prod_mul_distrib,prod_const]; ring
  change w k = _
  calc
    _ = a.coeff k := by
      unfold a; rw [Polynomial.finsetSum_coeff,sum_eq_single k]
      · simp
      · intro j _ hj; simp [Polynomial.coeff_monomial,hj]
      have : k∈range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left ..))
      exact fun hn => False.elim (hn this)
    _ = _ := by simp only [he,b,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,Finset.sum_filter,W]

lemma shard_size (s : R.Mode) (p : (parts R).Mode) (hp : p∈shards R s) : p.val.card ≤ Fintype.card ι := by
  have h : s.val.card = ∑ i∈p.val,i.val.val.card := by rw [← (chooses ..).mp hp]; exact card_biUnion (parts_wise _)
  refine le_trans ?_ (card_le_univ s.val)
  rw [h,Finset.card_eq_sum_ones]
  exact sum_le_sum fun i _ => card_pos.mpr i.property

/-- Explicit ordinary cumulant (partition inversion). Require unit vacuum
`hx` AND a marked read. -/
theorem cumulant_partition {x : Poly R} (hx : x.part R.quiet = 1) (s : Multi.Hot R) :
    (connected x).part s.val =
      ∑ p∈shards R s.val,
        (-1:ℂ)^(p.val.card-1) * ((p.val.card-1).factorial : ℂ) * ∏ b∈p.val,x.part b.val := by
  let w (p : (parts R).Mode) := ∏ b∈p.val,x.part b.val
  let a (p : (parts R).Mode) := (-1:ℂ)^(p.val.card-1) * (((p.val.card-1).factorial : ℂ)) * w p
  let n := Fintype.card ι
  have hy (b : Multi.Hot R) : (x-1).part b.val = x.part b.val := by
    have hh : b.val ≠ R.quiet := fun H => b.property.ne_empty (congrArg Subtype.val H)
    simp [Extra.Trajectories.part_sub, hh]
  have hq : (x-1).part R.quiet = 0 := by simp [Extra.Trajectories.part_sub,hx]
  have hpos (p : (parts R).Mode) (hp : p ∈ shards R s.val) : 0 < p.val.card := by
    refine Nat.pos_of_ne_zero fun he => ?_
    have hu := chooses s.val p |>.mp hp
    rw [show p=(parts R).quiet from Subtype.ext (card_eq_zero.mp he),unionOf_empty] at hu
    exact s.property.ne_empty (congrArg Subtype.val hu.symm)
  have hw (k : ℕ) :
      (((-1 : ℂ)^k / (k+1 : ℂ)) • (x-1)^(k+1)).part s.val =
        ∑ i∈(shards R s.val).filter (fun p => p.val.card-1=k), a i := by
    rw [show (shards R s.val).filter (fun p => p.val.card-1=k)=
      (shards R s.val).filter (fun p => p.val.card=k+1) from filter_congr fun j hj => by have := hpos j hj; omega]
    rw [Poly.part_smul]
    have he : ((k.factorial : ℂ)) * ((k+1).factorial:ℂ)⁻¹ = (k+1:ℂ)⁻¹ := by
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one,mul_inv_rev,← mul_assoc]
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero),one_mul]
    rw [div_eq_mul_inv, ← he, ← mul_assoc, mul_assoc (_ * _), number_factors hq,Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    unfold a w
    rw [(mem_filter.mp hi).2, Nat.add_sub_cancel]
    congr 1; exact prod_congr rfl fun b _ => hy b
  rw [connected_eq_logTable hx, logTable, Poly.part_sum]
  simp_rw [hw]
  exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_range.mpr (by have := shard_size _ p hp; have := hpos p hp; omega)) _

end Fin
end YM.RG02.Marks

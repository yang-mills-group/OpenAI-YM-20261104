import YangMills.WilsonProof.NativeSupport.Commissioned259.Cancellation

/-!
# Unit balls and arbitrary fixed field budgets
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Rake MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {V : Arenas G} {R : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    {n m H h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H)
    (he : ∀ i, e i ≤ H) (hh : h ≤ H)

/-- Power-series gap; this subtracts the full convolution, not yet the evaluation on the
separately cropped output vector. -/
def gap (V : Arenas G) (B : ℝ → Frames G)
    {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H)
    (he : ∀ i, e i ≤ H) {h : ℕ} (hh : h ≤ H) (x : Points n) (y : Points m)
    (η : ℝ) (u : Slots G d) (v : Slots G e) : PowerSeries ℂ :=
  measurement V B hd he x y η u v - ∑ q : Toon G h,
    farCf V u x (flash q) * center V B he y hh η (theory q) v

section Algebra
variable (x : Points n) (y : Points m) (η : ℝ) (u : Slots G d) (v : Slots G e)
local notation "μ" => measurement V B hd he x y η
local notation "M" => center V B he y hh η
local notation "Cₓ" => farCf V
local notation "Ξ" => gap V B hd he hh x y η

lemma near_extension : μ u v = ∑ b : BasisSlots G d, C (coordinates b u) * μ (word b) v := by
  ext1 k; simp_rw [map_sum, measurement, coeff_C_mul, coeff_mk]
  nth_rw 1 [word_sigma u (inserted V B hd he x y η k), _root_.sum_apply]
  rfl

lemma far_extension : μ u v = ∑ b : BasisSlots G e, C (coordinates b v) * μ u (word b) := by
  ext1 k; simp_rw [map_sum, measurement, coeff_C_mul, coeff_mk]; exact word_sigma v _

lemma center_extension (a : Sec G h) : M a v = ∑ b : BasisSlots G e, C (coordinates b v) * M a (word b) := far_extension ..

lemma components (b : BasisSlots G d) (q : Q G) : Cₓ (word b) x q = FarCoefficients V (names b) x q := by
  rw [farCf, Finset.sum_eq_single b]
  · rw [coordinates]; simp_rw [word, pivotδ, if_true, Finset.prod_const_one, map_one, one_mul]
  · intro c _ h; obtain ⟨i,hi⟩ := Function.ne_iff.mp h; rw [coordinates, Finset.prod_eq_zero (i:=i) (Finset.mem_univ i) (by rw [word,pivotδ,if_neg (Ne.symm hi)]), map_zero, zero_mul]
  · simp

lemma cf_extension (q : Q G) : Cₓ u x q = ∑ b : BasisSlots G d, C (coordinates b u) * Cₓ (word b) x q := by
  simp_rw [components]; rfl

lemma gap_near : Ξ u v = ∑ b : BasisSlots G d, C (coordinates b u) * Ξ (word b) v := by
  rw [gap, near_extension]
  conv_lhs => rhs; arg 2; intro q; rw [cf_extension, Finset.sum_mul]
  simp_rw [gap, mul_sub, Finset.mul_sum, ←mul_assoc]; rw [Finset.sum_sub_distrib, Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)]

lemma gap_far : Ξ u v = ∑ b : BasisSlots G e, C (coordinates b v) * Ξ u (word b) := by
  rw [gap, far_extension]
  conv_lhs => rhs; arg 2; intro q; rw [center_extension, Finset.mul_sum]; arg 2; intro b; rw [mul_left_comm]
  simp_rw [gap, mul_sub, Finset.mul_sum]; rw [Finset.sum_sub_distrib, Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)]

-- Since the adjusted kernel is multilinear, the crop at fixed Far fields is a linear map on the through-h outputs
-- (without any complex conjugation).
def centerCoeff (V : Arenas G) (B : ℝ → Frames G) {e : Fin m → ℕ}
    (he : ∀ i, e i ≤ H) {h : ℕ} (hh : h ≤ H) (y : Points m) (η : ℝ) (v : Slots G e) (k : ℕ) : Sec G h →ₗ[ℂ] ℂ :=
  let X := inserted V B (d:=fun _=>h) (fun (_:Fin 1)=>hh) he (0:Points 1) y η k
  { toFun := fun a => X (fun _=>a) v
    map_add' := fun a b => by
      have ha (c : Sec G h) : (fun (_ : Fin 1) => c) = update (fun (_: Fin 1)=>a) 0 c := funext (Fin.forall_fin_one.mpr (by simp))
      rw [ha (a+b), MultilinearMap.map_update_add, ← ha, ← ha, _root_.add_apply]
    map_smul' := fun c a => by
      have ha (b : Sec G h) : (fun (_ : Fin 1) => b) = update (fun (_: Fin 1)=>a) 0 b := funext (Fin.forall_fin_one.mpr (by simp))
      rw [ha (c • a), MultilinearMap.map_update_smul, ← ha]; rfl }

lemma reading_linear (p : ℕ) (t : ℝ) (c : Toon G h → ℂ) :
    crop p t (M (∑ q : Toon G h, c q • theory q) v) =
      ∑ q : Toon G h, c q * crop p t (M (theory q) v) := by
  have eqn (a : Sec G h) (k : ℕ) : coeff k (M a v) = centerCoeff V B he hh y η v k a := by
    rw [center, measurement, coeff_mk]; rfl
  simp_rw [crop_apply, eqn, map_sum, _root_.map_smul, smul_eq_mul, Finset.mul_sum,
    mul_left_comm ((t:ℂ)^_)]
  rw [Finset.sum_comm]
end Algebra

section Bounded
variable {U : ℝ} {I : Type} {K : Set (Points n)} {S : Set (Points m)}
    {r : I → Slots G d} {w : I → Slots G e} {x : I → Points n} {y : I → Points m}
    (hU : 0 ≤ U) (L : Law V R B) (P : O.Canon.Physical V R B)
    (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    (hu : ∀ i, r i ∈ Balls U G d) (hv : ∀ i, w i ∈ Balls U G e) (hx : ∀ i, x i ∈ K) (hz : ∀ i, y i ∈ S)
    (p : ℕ) (q : Toon G h)

include hU P hK hc hx hu in
lemma through_horizon (q : Q G) (k : ℕ) : ∃ A : ℝ, ∀ i,
    ‖coeff k (farCf V (r i) (x i) q)‖ ≤ A := by
  choose a ha using fun b : BasisSlots G d => Fcompact P (names b) hK hc q k
  refine ⟨ ∑ b : BasisSlots G d, U^n * |a b|, fun i=> ?_⟩
  simp_rw [farCf,map_sum,coeff_C_mul]
  apply (norm_sum_le ..).trans
  refine Finset.sum_le_sum fun b _=> ?_
  rw [norm_mul]; exact mul_le_mul (coord_price hU _ (hu i) _) ((ha b _ (hx i)).trans (le_abs_self _)) (norm_nonneg _) (pow_nonneg hU _)

include hU hu in
lemma coeff_pay (b : BasisSlots G d) : ChargeP p 0 (fun (i : I) (_ : ℝ) =>
    C (coordinates b (r i))) := ChargeP.constants (Rain.cash ⟨_,fun i => coord_price hU _ (hu i) _⟩)

include L P hU hS hy hz hv
lemma center_charge : ChargeP p (heft (flash q) : ℝ) (fun i s=>
    center V B he (squeeze (-s) (y i)) hh (-s) (theory q) (w i)) := by
  simp_rw [center_extension he hh _ _ (w _)]
  refine ChargeP.sum _ fun b _ => ?_
  exact ChargeP.times (coeff_pay hU hv p b)
    ((basis_center_charge L P he hh hS hy (names b) q (included b) p).pull
      (fun i : I => (⟨y i, hz i⟩ : ↥S)))
include hK hc hx hu
lemma full_charge (h : ℕ) : ChargeP p 0 (fun i s=>
    measurement V B hd he (x i) (squeeze (-s) (y i)) (-s) (r i) (w i)) := by
  simp_rw [near_extension hd he _ _ _ (r _), far_extension hd he _ _ _ (word _) (w _)]
  refine ChargeP.sum _ fun b _ => ChargeP.times (coeff_pay hU hu p b) ?_
  refine ChargeP.sum _ fun j _ => ChargeP.times (coeff_pay hU hv p j) ?_
  exact (basis_full_charge L P hd he hK hc hS hy (names b) (names j) (included b) (included j) p h).pull (fun i => ((⟨x i, hx i⟩ : ↥K), (⟨y i,hz i⟩ : ↥S)))
lemma gap_charge : ChargeP p ((h:ℝ)+1) (fun i s =>
    gap V B hd he hh (x i) (squeeze (-s) (y i)) (-s) (r i) (w i)) := by
  simp_rw [gap_near hd he hh _ _ _ (r _), gap_far hd he hh _ _ _ (word _) (w _)]
  refine ChargeP.sum _ fun b _ => ChargeP.times (coeff_pay hU hu p b) ?_
  refine ChargeP.sum _ fun j _ => ChargeP.times (coeff_pay hU hv p j) ?_
  simp_rw [gap, components]
  exact (basis_gap_charge L P hd he hh hK hc hS hy (names b) (names j) (included b) (included j) p).pull (fun i => ((⟨x i, hx i⟩ : ↥K), (⟨y i,hz i⟩ : ↥S)))
end Bounded
end YM.FVA2.GradedFar259

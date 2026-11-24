import YM.WilsonMS.Beta.Horn
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
/-!
# Gaussian moments inside the Landau shell calculation

Here `moment` computes via directional IBP. Volume in physical four-plane
normalization. Needed to integrate Lorentz moment polynomials, not using
anisotropic approximation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue.HeatPapers
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native
open Horn
open _root_.YM.PertExtension
open RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open Complex (I)
open Papers
open scoped Topology ContDiff BigOperators ENNReal
variable {α : ℝ} (h : 0 < α)

lemma amountP : (∫ q, (Beam α h).kern q ∂mplane) = Real.pi ^ 2 / α ^ 2 / (2 * Real.pi) ^ 4 := by
  have hv p : (Beam α h).kern p = ∏ i : Axis, exp (-α * p i ^ 2) := by
    rw [← Real.exp_sum, kernel_val]
    simp [Momentum.sq, Finset.mul_sum]
  unfold mplane covMeasure
  rw [integral_smul_measure]
  simp_rw [hv]
  let C : ℝ := 2 * Real.pi
  have hx : C ≠ 0 := by
    unfold C
    exact (by positivity)
  rw [show (volume : Measure QP) = Measure.pi (fun i : Axis => (volume : Measure ℝ)) from rfl,
    integral_fintype_prod_eq_prod (f := fun (_ : Axis) (x : ℝ) => exp (-α * x ^ 2))]
  simp_rw [integral_gaussian α]
  simp only [Finset.prod_const, card_univ, show Fintype.card Axis = 4 from rfl]
  have hQ : 0 < Real.pi / α := div_pos pi_pos h
  have hh : ((Real.sqrt (Real.pi / α)) ^ 4) = (Real.pi / α) ^ 2 := by
    rw [show 4 = (2 : ℕ) * 2 from rfl, pow_mul, sq_sqrt hQ.le]
  rw [hh, ENNReal.toReal_ofReal]
  simp only [smul_eq_mul]
  field_simp
  positivity

lemma beam_price (a : Axis) : (Beam α h).P (Detect.spike a) = (2 * α) • lambda a := by
  apply LinearMap.ext
  intro t
  change 2 * α * (∑ i : Axis, Detect.spike a i * t i) = 2 * α * t a
  rw [Finset.sum_eq_single a ?_ (by simp), Detect.spike_self, one_mul]
  intro i _ hi
  simp [hi]

local notation "Y" => Beam α h
local notation "V" => HeatPapers.Poly
set_option quotPrecheck false
local notation "Φ" => Papers.opening mplane (Beam α h)

lemma net_order (p : HeatPapers.Poly) :
    ∫ q, (p.val q) * exp (-α * q.sq) ∂mplane = (Real.pi ^ 2 / α ^ 2 / (2 * Real.pi) ^ 4) * Φ p := by
  let A := Beam α h
  let q := mplane
  have ht := Splice.positive (Beam α h) mplane
  rw [← amountP h]
  change _ = (∫ p, A.kern p ∂q) * A.average q p.val
  unfold GaussianScore.Law.average
  unfold A q
  simp only [Pi.mul_apply, kernel_val]
  simp only [kernel_val] at ht
  rw [mul_comm, div_mul_cancel₀ _ ht.ne']

abbrev Shield (a : Axis) (P : HeatPapers.Poly) : Prop :=
  ∀ (x : QP) (t : ℝ), P.val (x + t • Detect.spike a) = P.val x

lemma omitting (p p' : HeatPapers.Poly) (a : Axis)
    (hv :
      ∀ x : QP,
        ∀ t : ℝ,
          HasDerivAt (fun t : ℝ => p.val (x + t • Detect.spike a)) (p'.val (x + t • Detect.spike a))
            t) :
    Φ p' = 2 * α * Φ (p * petal a) := by
  let s := Detect.spike a
  let X := Beam α h
  let Q := mplane
  let H := Papers.useful Q X
  obtain ht :=
    GaussianScore.Law.translation_lemma X s (Papers.applies p).2 (Papers.applies p).1
      (Papers.applies p').2 (Papers.applies p').1 hv Q
  have hh (q : QP) : (X.P s) q = ((2 * α) • petal a : HeatPapers.Poly).val q := by
    rw [beam_price]
    rfl
  let f := (2 * α) • (p * petal a : HeatPapers.Poly)
  have hp : p'.val - p.val * (X.P s) = (p' - f).val := by
    ext1 q
    simp only [Pi.sub_apply, Pi.mul_apply, hh]
    change _ = p'.val q - ((2 * α) * (p.val q * _))
    change _ - (p.val q * ((2 * α) * _)) = _
    rw [mul_left_comm (p.val q)]
  rw [hp] at ht
  have hu : Φ (p' - f) = 0 := by
    change X.average Q _ = 0
    rw [GaussianScore.Law.average]
    rw [ht, zero_div]
  have he := map_sub Φ p' f
  rw [hu] at he
  exact (sub_eq_zero.mp he.symm).trans (map_smul Φ _ _)

def nearer (i : Axis) (d : ℝ) :=
  petal i - spring d

def moment (α d : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -d
  | i + 2 => (i + 1 : ℕ) / (2 * α) * moment α d i - d * moment α d (i + 1)
variable (v : V)

lemma bill_ray (a : Axis) (d : ℝ) (p : V) (hP : Shield a p) (i : ℕ) :
    Φ (nearer a d ^ i * p) = moment α d i * Φ p := by
  let x := petal a
  let f := nearer a d
  change Φ (f ^ i * p) = _
  have hv (y : QP) (t : ℝ) : meterR y (spring t * p) = t * p.val y := by
    rw [map_mul, atR]
    rfl
  have he (k : ℕ) : f ^ (k + 1) * p = f ^ k * p * petal a - d • (f ^ k * p) := by
    rw [pow_succ, Algebra.smul_def]
    change f ^ k * (petal a - spring d) * p = _ - spring d * _
    ring
  have hF (y : QP) (u : ℝ) : f.val (y + u • Detect.spike a) = f.val y + u := by
    change meterR _ (petal a - spring d) = meterR y (petal a - spring d) + u
    rw [map_sub, map_sub, atP, atP, atR, atR]
    change _ + u * Detect.spike a a - _ = _
    rw [Detect.spike_self, mul_one]
    ring
  have hm (y : QP) (z : ℝ) : HasDerivAt (fun u => f.val (y + u • Detect.spike a)) 1 z := by
    simp_rw [hF]
    exact (hasDerivAt_id' _).const_add _
  have hK (y : QP) (z : ℝ) :
    HasDerivAt (fun u => p.val (y + u • Detect.spike a)) ((0 : V).val (y + z • Detect.spike a)) z := by
    rw [funext (fun u => hP y u)]
    exact hasDerivAt_const ..
  induction i using Nat.strong_induction_on with
  | h i ih =>
    match i with
    | 0 => rw [pow_zero, one_mul, moment, one_mul]
    | 1 =>
      rw [he 0, pow_zero, one_mul, map_sub, _root_.map_smul, moment]
      obtain hT := omitting h p 0 a hK
      rw [map_zero] at hT
      rw [(mul_eq_zero.mp hT.symm).resolve_left (by positivity)]
      ring_nf
    | k + 2 =>
      rw [he (k + 1), map_sub, _root_.map_smul, moment]
      let b := f ^ (k + 1) * p
      let K := f ^ k * p
      let e := ((k + 1 : ℕ) : ℝ)
      have hz : Φ (e • K) = 2 * α * Φ (b * petal a) := by
        refine omitting h _ _ a fun y u => ?_
        have hr := ((hm y u).pow (k + 1)).mul (hK y u)
        convert! hr using 1
        change e * (f.val (y + u • Detect.spike a) ^ k * p.val (y + u • Detect.spike a)) = _
        simp only [show ((0 : V).val : QP → ℝ) = 0 from rfl, Pi.zero_apply, mul_zero, add_zero,
          mul_one, Nat.add_sub_cancel]
        ring
      have hE : Φ (b * petal a) = ((Φ K) * (e / (2 * α))) := by
        rw [_root_.map_smul] at hz
        unfold K at hz ⊢
        change e * _ = _ at hz
        field_simp
        linarith only [hz]
      rw [hE, show Φ K = _ from ih k (by omega), ih (k + 1) (by omega)]
      unfold e
      ring

lemma shield_num (v : ℝ) (a : Axis) : Shield a (spring v) := fun _ _ => rfl

lemma shield_atom {a b : Axis} (h : a ≠ b) : Shield a (petal b) := by
  intro x t
  change (x b + t * Detect.spike a b) = _
  simp only [spike_of_ne h.symm, mul_zero, add_zero]
  rfl
variable {a b : Axis} {p q : HeatPapers.Poly}

lemma Shield.product (h : Shield a p) (hh : Shield a q) : Shield a (p * q) := by
  intro x y
  change p.val _ * q.val _ = _
  rw [h, hh]
  rfl

lemma Shield.power (h : Shield a p) (i : ℕ) : Shield a (p ^ i) := by
  induction i with
  | zero =>
    rw [pow_zero]
    exact fun _ _ => rfl
  | succ i ih =>
    rw [pow_succ]
    exact ih.product h

lemma shield_near (h : a ≠ b) (i : ℕ) (v : ℝ) : Shield a (nearer b v ^ i) := by
  apply Shield.power
  intro x t
  change (petal _).val _ - (spring v).val _ = (petal _).val _ - _
  rw [shield_atom h, shield_num v]

def Cubicle (d : ℝ) (i j k l : ℕ) : HeatPapers.Poly :=
  nearer 0 d ^ i * (petal 1 ^ j * (petal 2 ^ k * petal 3 ^ l))

lemma along_R (d : ℝ) (i j k l : ℕ) :
    Φ (Cubicle d i j k l) = moment α d i * moment α 0 j * moment α 0 k * moment α 0 l := by
  have hx (a : Axis) : petal a = nearer a 0 := by rw [nearer, spring, map_zero, sub_zero]
  let A := nearer 1 0 ^ j
  let U := nearer 2 0 ^ k
  let C := nearer 3 0 ^ l
  have hC (a : Axis) (h : a ≠ 3) : Shield a C := shield_near h l 0
  have ht (a : Axis) (h : a ≠ 2) (hx : a ≠ 3) : Shield a (U * C) :=
    (shield_near h k 0).product (hC _ hx)
  rw [Cubicle, hx 1, hx 2, hx 3,
    bill_ray h _ d (A * (U * C))
      ((shield_near (show (0 : Axis) ≠ 1 from (by decide)) j 0).product
        (ht _ (by decide) (by decide)))
      i,
    bill_ray h _ _ _ (ht 1 (by decide) (by decide)) _, bill_ray h _ _ _ (hC 2 (by decide)) _,
    show Φ C = moment α 0 l from ?_]
  ring
  rw [← mul_one C, show Φ (C * 1) = _ from bill_ray h 3 0 1 (fun _ _ => rfl) l, Papers.starts,
    mul_one]
end YM.WilsonMS.BetaValue.HeatPapers

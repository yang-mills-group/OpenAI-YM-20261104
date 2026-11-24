import YM.Integration.WilsonIndependentMeasuredOpticalClock
import YM.Integration.WilsonIndependentMeasuredFaceSalary
import YM.Integration.WilsonIndependentMeasuredPeriod

/-! The original fitted coefficients and the licensed finite side in one
estimate. The roster and its physical source salary precede the paid order. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMeasuredOpticalDose
open Filter Lattice RG Source Labels XSpace PhysicalNext.Repeat.Legato
open WilsonIndependentRawPhysicalFaces (weight)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonPhysicalOrientedStencilPin (coordinates)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntrancePanel (Panel)
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (good : G.Simple) (V : XSpace.Run)
variable {n : ℕ} (d : Fin n → ℕ) (s : Finset (Fin n))
local notation "δ" => (fun i:s=>d i)
def head (d : ℕ) : ℝ := (2:ℝ)^(Finset.univ.sup (fun j:(R.family.labels.level d).Index =>
  Prod.snd ((R.family.labels.level d).grades j)))
def fare (powr : ℕ) (B : ℝ) : ℝ := ∏i:s,head R (d i)*(B*(1+G.slopeConstant)^powr)
variable {N per K f requested power age : ℕ} {B : ℝ} (file : Filed R d K)
  {fk : f ≤ K} {kn : K ≤ N} (A : Panel R d N per f K fk kn requested power age B)
  (station : A.slot=file.station) (axes : A.axis=file.A N per)
local notation "row" => coordinates R d (N:=N) (per:=per) file A.names A.turn
local notation "H" => R.family.path.levels.clock.hatBeta

include station axes in
theorem original {i : ℕ} (positive : 0 ≤ B) (thermal : H K ≤ (1+G.slopeConstant)*(V.den i : ℝ)) :
    ∑a:Columns R δ,‖weight R d row s a‖ ≤ fare R d s power B*(V.den i : ℝ)^(power*s.card) := by
  have hot : 0 ≤ H K := (zero_lt_one.trans (R.family.path.levels.fits.delayed K)).le
  have stage := pow_le_pow_left₀ hot thermal power
  have wage := WilsonIndependentMeasuredFaceSalary.original R d s file A station axes
  let X : s → ℝ := fun j=>head R (d j)
  change _ ≤ ∏j:s,X j*(B*(H K)^power) at wage
  apply wage.trans
  calc ∏j:s,X j*(B*(H K)^power) ≤ ∏j:s,X j*(B*((1+G.slopeConstant)*(V.den i : ℝ))^power) := by
           apply Finset.prod_le_prod
           · intro j _
             exact mul_nonneg (by dsimp [X,head];positivity) (mul_nonneg positive (pow_nonneg hot _))
           · intro j _
             exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left stage positive) (by dsimp [X,head];positivity)
       _ = (∏j:s,(X j*(B*(1+G.slopeConstant)^power))*(V.den i : ℝ)^power) := by
           apply Finset.prod_congr rfl
           intro j _
           rw [mul_pow]
           ring
       _ = fare R d s power B*(V.den i : ℝ)^(power*s.card) := by
           rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,pow_mul]
           rfl

include good station axes in
theorem signed {i p k : ℕ} (positive : 0 ≤ B) (thermal : H K ≤ (1+G.slopeConstant)*(V.den i : ℝ))
    (late : 8*(power*s.card+p) ≤ i) (C : ℝ) (budget : 0 ≤ C) (Y : Columns R δ → ℂ)
    (paid : ∀a,‖Y a‖ ≤ C*(1+Real.log ((V.step i).p.side.val : ℝ))^k*((V.step i).p.side.val : ℝ)^(-(1/4:ℝ))) :
    ‖∑a:Columns R δ,weight R d row s a*Y a‖ ≤
      (fare R d s power B*C*(1+8*((k:ℝ)+1))^k)*(V.step i).spacing^p := by
  let μ:ℝ := (V.step i).p.side.val
  let receipt:=C*(1+Real.log μ)^k*μ^(-(1/4:ℝ))
  have cap : 1 ≤ μ := by dsimp only [μ]; exact_mod_cast (V.step i).p.side.pos
  have rated : 0 ≤ receipt := mul_nonneg (mul_nonneg budget (pow_nonneg (by linarith [Real.log_nonneg cap]) _))
      (Real.rpow_nonneg (zero_le_one.trans cap) _)
  have funds : 0 ≤ fare R d s power B := Finset.prod_nonneg fun j _=>
    mul_nonneg (by unfold head;positivity) (mul_nonneg positive (pow_nonneg (by linarith [Gauge.slopeConstant_pos good]) _))
  apply WilsonIndependentMeasuredPeriod.original V i (power*s.card) p k late _ _ _ funds budget
  calc ‖∑a:Columns R δ,weight R d row s a*Y a‖ ≤ ∑a:Columns R δ,‖weight R d row s a*Y a‖ := norm_sum_le ..
       _ ≤ ∑a:Columns R δ,‖weight R d row s a‖*receipt := by
         apply Finset.sum_le_sum
         intro j _
         rw [norm_mul]
         exact mul_le_mul_of_nonneg_left (paid j) (norm_nonneg _)
       _ = (∑a:Columns R δ,‖weight R d row s a‖)*receipt := by rw [Finset.sum_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_right (original R V d s file A station axes positive thermal) rated

end YM.Integration.WilsonIndependentMeasuredOpticalDose

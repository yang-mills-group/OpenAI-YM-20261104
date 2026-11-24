import YM.Integration.ManuscriptQLocalGaussianQuartic

/-! Every surviving split of the rooted square of the actual affine residual. The legs
are occurrences in an ordered list and need not be distinct. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianSourcePartitions
open Function Filter Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarIdealSquare
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section Leibniz
variable {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def splits (v : ι→X) (f : X→ℝ) (l : List ι) : ℝ :=
  ∑ m : Masks l, if 2 ≤ (lo l m).length ∧ 2 ≤ (hi l m).length then
    jet v f (lo l m) 0 * jet v f (hi l m) 0 else 0

theorem short (v : ι→X) (f : X→ℝ) (l : List ι) (few : l.length ≤ 3) : splits v f l=0 := by
  apply Finset.sum_eq_zero
  intro m _
  have h := lengths l m
  exact if_neg (by omega)

theorem square (v : ι→X) (f : X→ℝ) (l : List ι) (hl : ContDiffAt ℝ l.length f 0)
    (h₁ : ContDiffAt ℝ 1 f 0) (h₀ : f 0=0) (deriv : fderiv ℝ f 0=0) :
    jet v (fun B => f B*f B) l 0 = splits v f l := by
  have h := leibniz v (ContinuousLinearMap.mul ℝ ℝ) l (A:=f) (B:=f) hl hl
  change jet v (fun B => f B*f B) l 0 = ∑ m : Masks l,jet v f (lo l m) 0*jet v f (hi l m) 0 at h
  rw [h]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs with both
  · rfl
  · by_cases small : (lo l m).length ≤ 1
    · rw [PhysicalAffineScalarIdealGrading.short v h₁ h₀ deriv _ small,zero_mul]
    · rw [PhysicalAffineScalarIdealGrading.short v h₁ h₀ deriv _ (by omega : (hi l m).length ≤ 1),mul_zero]

private theorem zero_jet (v : ι→X) (l : List ι) : jet v (fun _ => (0:ℝ)) l 0=0 := by
  cases l with
  | nil => exact zeroth v _ 0
  | cons a l => exact jet_const v (a::l) (by simp) 0 0

private theorem rows {κ : Type*} [Fintype κ] (owns : κ→Prop) [DecidablePred owns]
    (v : ι→X) (f : κ→X→ℝ) (l : List ι) (hl : ∀ i, ContDiffAt ℝ l.length (f i) 0)
    (h₁ : ∀ i, ContDiffAt ℝ 1 (f i) 0) (h₀ : ∀ i, f i 0=0) (deriv : ∀ i, fderiv ℝ (f i) 0=0) :
    jet v (fun B => ∑ i,if owns i then f i B*f i B else 0) l 0 =
      ∑ i,if owns i then splits v (f i) l else 0 := by
  let held i B := if owns i then f i B*f i B else 0
  have hh (i : κ) : ContDiffAt ℝ l.length (held i) 0 := by
    by_cases hi : owns i
    · simpa only [held,hi,if_true] using (hl i).mul (hl i)
    · simp only [held,hi,if_false]; exact contDiffAt_const
  change jet v (fun B => ∑ i,held i B) l 0 = _
  rw [jet_sum v l Finset.univ held (fun i _ => hh i)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : owns i
  · simp only [held,hi,if_true]
    exact square v (f i) l (hl i) (h₁ i) (h₀ i) (deriv i)
  · simp only [held,hi,if_false]; exact zero_jet v l
end Leibniz

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Marker.Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.alloy.B.a.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.alloy.B.a.clock.schedule.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "rp" => PhysicalAffineScalarComparison.rowRoot (G:=G) S

def source {ι : Type*} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (v : ι→E) (l : List ι) : ℝ :=
  ∑ i : Rows.Receipt G S, if rp i=o then splits v (fun B => residual T k F B i) l else 0

theorem below_four {ι : Type*} (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀)
    (v : ι→E) (l : List ι) (few : l.length ≤ 3) : source R d k F o v l=0 := by
  unfold source
  simp only [short v _ l few,ite_self,Finset.sum_const_zero]

theorem mass_jet [Fintype I] {ι : Type*} {n : ℕ} {δ C : ℝ} (k : (S).Choices) (F : Forest (S).ratio)
    (o : Site c₀) (H : ConditionalAffineLoadPrices.Paid rp δ C n (residual T k F))
    (one : 1 ≤ n) (v : ι→E) (l : List ι) (hl : l.length ≤ n) :
    jet v (mass T k F o) l 0 = source R d k F o v l := by
  let row (i : Rows.Receipt G S) (B : E) := residual T k F B i
  have smooth (i : Rows.Receipt G S) : ContDiffAt ℝ n (row i) 0 :=
    (TestD.evaluate i ()).contDiff.contDiffAt.comp 0 H.smooth
  have funding := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  have branches : (S).patch.Branches (S).kernel G := funding.knobs.symm ▸ funding.kernel
  have hz (i : Rows.Receipt G S) : row i 0=0 := congrFun (PhysicalAffineScalarIdealSquare.zero T k branches F) i
  apply rows (fun i => rp i=o) v row l (fun i => smooth_of_le (smooth i) hl)
    (fun i => smooth_of_le (smooth i) one) hz
  intro i
  exact PhysicalAffineScalarIdealGrading.derivative_zero ((smooth_of_le (smooth i) one).differentiableAt (by norm_num))
    (hz i) (ManuscriptQLocalIdealSquare.slope R d k F i)

private theorem signed_power {g : ℝ} (hg : 0 < g) {j : ℕ} (hj : 2 ≤ j) :
    -(2*g^2)⁻¹*g^j = -(g^(j-2)/2) := by
  have h := PhysicalAffineScalarIdealGrading.coefficient hg hj
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (inv_nonneg.mpr (by positivity))) (by positivity))] at h
  linarith

theorem graded_jet [Fintype I] {ι : Type*} {n : ℕ} {δ C g : ℝ} (k : (S).Choices) (F : Forest (S).ratio)
    (o : Site c₀) (H : ConditionalAffineLoadPrices.Paid rp δ C n (residual T k F)) (one : 1 ≤ n)
    (hg : 0 < g) (v : ι→E) (l : List ι) (hl : l.length ≤ n) :
    jet v (ManuscriptQLocalIdealSquare.graded R d k F g o) l 0 =
      -(g^(l.length-2)/2)*source R d k F o v l := by
  rw [ManuscriptQLocalIdealSquare.grades R d k F g o H v l hl, mass_jet R d k F o H one v l hl]
  by_cases enough : 2 ≤ l.length
  · rw [signed_power hg enough]
  · rw [below_four R d k F o v l (by omega),mul_zero,mul_zero]

end YM.Integration.WilsonGaussianSourcePartitions

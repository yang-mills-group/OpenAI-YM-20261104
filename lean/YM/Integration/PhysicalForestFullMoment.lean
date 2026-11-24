import YM.Integration.PhysicalForestMarkedRay

/-! Full finite Fk on the original held forest in absolute group-field coordinates, at every incoming marked face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalForestFullMoment
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open FreeResolvent Comparison.RG02 MeasureTheory Stationary Marker Multi Next.SectorChange
open PhysicalForestAction
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
variable {p : Clip} {P : PathData G} {O : ChartRatio G}
variable {V : Type} [DecidableEq V] {C : Census V}
variable (M : Matrix (Woods G f) (Woods G c) ℝ) (K : Bulk.Kernel S p P O)
variable (x : fieldDir G c 1) (z : Precision.Key F G → ℝ)


open PhysicalForestRay


private theorem sums {A B:Type*} (a:ℕ→A→ℝ) (b:ℕ→B→ℝ) (x₀:A) (y:B)
    (same:∀ j,a j x₀=b j y) (k n:ℕ) :
    PertExtension.Series.Radial.expsum a k n x₀=PertExtension.Series.Radial.expsum b k n y := by
  have powers (i:ℕ):∀ d, PertExtension.Series.Zone.TaylorPow a i d x₀=
      PertExtension.Series.Zone.TaylorPow b i d y := by
    induction i with
    | zero => intro d; rfl
    | succ i ih =>
      intro d
      simp only [PertExtension.Series.Zone.TaylorPow,PertExtension.Series.Zone.mul]
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg₂ (·*·) (ih j.1) (same j.2)
  apply Finset.sum_congr rfl
  intro i _
  rw [powers]

open PhysicalForestMarkedRay PertExtension.Series Assembly Multi Order PowerSeries
variable [Fintype V]

/-- The scalar includes the full old field action and its change of Haar volume. -/
def scalar (t:S.Choices) (W:Bulk.Colors C G f) (d:ℕ) : ℝ :=
  (d.factorial:ℝ)⁻¹ * iteratedDeriv d (chartAction S F M K x z t W) 0

def layer (t:S.Choices) (W:Bulk.Colors C G f) (n:ℕ) (y:Precision.Key F G→ℝ) : ℝ :=
  -scalar S F M K x y t W (n+2) + if n=0 then scalar S F M K x y t W 2 else 0

def roster (t:S.Choices) (W:Bulk.Colors C G f) : PTable C :=
  realCurve C (fun n=>Radial.expsum (layer S F M K x t W) n n z) *
    markExp (PowerSeries.mk fun n=>lit C (fun J=>readJet (W.power J + n)
      (chartMark S F M K x z W J)))

theorem polynomial (t:S.Choices) (W:Bulk.Colors C G f) (well:Bulk.Well W)
    (hM:M = reveal G S F * ((reveal G S F).transpose * M)) :
    expansions W.power (Bulk.markFn S F W) (Bulk.geometric K F t W) (Bulk.translated K F x z) =
      roster S F M K x z t W := by
  have vacuum (j:ℕ):Radial.jet (Bulk.geometric K F t W) j (Bulk.translated K F x z)=
      scalar S F M K x z t W j :=
    PhysicalForestRay.coefficient S F M K x z t W well hM j
  have step (j:ℕ):Radial.layers (Bulk.geometric K F t W) j (Bulk.translated K F x z)=
      layer S F M K x t W j z :=by simp only [Radial.layers,layer,vacuum]
  have read (j:ℕ):=sums _ _ _ _ step j j
  unfold expansions roster curve markLetter
  simp only [read,PhysicalForestMarkedRay.coefficient S F M K x z t W well _ hM]

/-- Every ordinary proper subword of the authentic finite normalized Wick table
uses the very same covariance and the jointly transformed original nonlinear chart. -/
theorem original (t:S.Choices) (W:Bulk.Colors C G f) (well:Bulk.Well W)
    (hM:M = reveal G S F * ((reveal G S F).transpose * M))
    {r:ℕ} (J:C.Mode) (e:Index r) :
    (Bulk.Fk K F t W x r).part (Join.pair J e) =
      (e.val.card.factorial:ℂ) * ∫ y, ((PowerSeries.coeff e.val.card)
        (roster S F M K x y t W)).part J ∂Gaussian.cloud (K.covariance F t) := by
  rw [Bulk.table]
  apply congrArg ((e.val.card.factorial:ℂ)*·)
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun y=>?_)
  exact congrArg (fun P:PTable C=>((PowerSeries.coeff e.val.card) P).part J)
    (polynomial S F M K x y t W well hM)

end YM.Integration.PhysicalForestFullMoment

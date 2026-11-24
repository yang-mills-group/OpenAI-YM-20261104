import YM.Integration.FVA1Physical.CommonCover.PhysicalInheritedBill

/-! Sum the inherited charge under the true projection law. All predictor
tags share the same incoming mixed source and the same physical vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter Function Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual Push.SectorMeasure
open scoped Classical
variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I}
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Rep G f} {O : ChartRatio G}
  (K : Bulk.Kernel S P.clip P.path O) (F : Forest S.ratio) (g : ℝ)
  (x : fieldDir G c 1) (W : Bulk.Colors R G f) (D : Lit R (Config G f)) (w : I→ℝ) (Q : Poly R)

/-- Local relative charge per unit of actual vacuum mass. -/
def relativeInlet (U : Config G f) : ℝ :=
  let r := remainderVac W U g P
  let M := model g (levelScalar P) W K U
  Real.exp (Poly.price w (markedLog g U W)) * (Real.exp (mixedBill (P:=P) W D g w U)-1) +
    max 1 (Real.exp r) * |r| * Poly.price w (unitScale M-Q)

theorem calmBill_factored (t : S.Choices) (heat : P.beta=temperature g) (y : F.Slice G)
    (calm : F.drape y∈Calm P.p) :
    calmBill K F t g x W D w Q y =
      (taggedKernel S (temperature g) t (F.drape y) (sample g x)*P.eval (F.drape y)) *
        relativeInlet K g W D w Q (F.drape y) := by
  let U := F.drape y
  let r := remainderVac W U g P
  let b := weight g (levelScalar P) U W P.clip P.path
  have positive : 0<P.eval U := healthy_live calm
  have recover : P.eval U * Real.exp r=b := by
    rw [base_entry W g heat calm,mul_assoc,←Real.exp_add,show -remainderVac W U g P+r=0 from neg_add_cancel _,Real.exp_zero,mul_one]
  have bigger : max (P.eval U) b = P.eval U * max 1 (Real.exp r) := by
    rw [mul_max_of_nonneg _ _ positive.le,mul_one,recover]
  change _=_
  unfold calmBill relativeInlet
  change _*(P.eval U*_+max (P.eval U) b * |r| * _) = (_*P.eval U)*(_+max 1 (Real.exp r) * |r| * _)
  rw [bigger]
  ring

/-- A single price for the normalized full incoming table on the mask
costs at most that price times the true joint tag-and-field mass of the
mask. There is no division by an estimated vacuum and no number-of-tags
prefactor. -/
theorem all_tags_older (floor : Floor P D) (well : Bulk.Well W)
    (hw : ∀i,0<w i) (heat : P.beta=temperature g) (A : Set (F.Slice G))
    (hA : MeasurableSet A) (inside : ∀y∈A,F.drape y∈Calm P.p)
    (cap : ℝ) (localFee : ∀y∈A,relativeInlet K g W D w Q (F.drape y)≤cap) :
    let E := ∑t:S.Choices,charge (F.order G) (older K F t g (levelScalar P) x W A D)
    Poly.price w (E-E.part R.quiet • Q) ≤
      (∫y in A, S.density (temperature g) (F.drape y) (sample g x)*P.eval (F.drape y) ∂F.order G)*cap := by
  intro E
  let Z := fun t:S.Choices=>charge (F.order G) (older K F t g (levelScalar P) x W A D)
  let J := fun (t:S.Choices) (y:F.Slice G)=>taggedKernel S (temperature g) t (F.drape y) (sample g x)*P.eval (F.drape y)
  have integr (t:S.Choices) : Integrable (J t) (F.order G) := by
    have good := good_slice F t (sample g x) (temperature g) K.branches floor.safe
    apply (good R.quiet).re.congr
    apply Eventually.of_forall
    intro y
    change (((taggedKernel S (temperature g) t (F.drape y) (sample g x):ℝ):ℂ)*(D (F.drape y)).part R.quiet).re=_
    rw [floor.vacancy,←Complex.ofReal_mul]
    rfl
  have centered : E-E.part R.quiet • Q = ∑t:S.Choices,(Z t-(Z t).part R.quiet • Q) := by
    change (∑t,Z t)-(∑t,Z t).part R.quiet • Q=_
    rw [Poly.part_sum,Finset.sum_smul,sum_sub_distrib]
  rw [centered]
  apply (Poly.batch hw _ _).trans
  calc
    _ ≤ ∑t:S.Choices, ∫y in A,J t y*cap ∂F.order G := by
      apply sum_le_sum
      intro t _
      apply represented_older K F t g x W D w Q floor well hw heat A hA inside
        (fun y=>J t y*cap) ((integr t).integrableOn.mul_const cap)
      intro y hy
      rw [calmBill_factored K F g x W D w Q t heat y (inside y hy)]
      exact mul_le_mul_of_nonneg_left (localFee y hy) (mul_nonneg (kernel_nonneg ..) (healthy_live (inside y hy)).le)
    _ = _ := by
      rw [←integral_finsetSum _ (fun t _=>(integr t).integrableOn.mul_const cap),←integral_mul_const]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change (∑t:S.Choices,taggedKernel S (temperature g) t (F.drape y) (sample g x)*P.eval (F.drape y)*cap)=_
      rw [←Finset.sum_mul,←Finset.sum_mul]
      rfl

end YM.Integration.FVA1Physical.OlderPrice

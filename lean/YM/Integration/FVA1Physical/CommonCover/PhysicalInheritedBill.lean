import YM.Integration.FVA1Physical.CommonCover.OriginalInletLog

/-! Integrate the inherited charge with the full old census in the
actual conditional Haar law. The extensive vacuum mismatch has cancelled
before this estimate is taken. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter Function Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual Push.SectorMeasure
open scoped Classical

variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I}

omit [Fintype I] in
private theorem center_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (Z : Lit R X) (good : Good μ Z) (Q : Poly R) (w : I→ℝ) (hw : ∀i,0<w i) :
    Poly.price w (charge μ Z-(charge μ Z).part R.quiet • Q) ≤
      ∫ y, Poly.price w (Z y-(Z y).part R.quiet • Q) ∂μ := by
  let part := fun (s:R.Mode) (y:X)=> (Z y).part s-(Z y).part R.quiet*Q.part s
  have paid (s:R.Mode) : Integrable (part s) μ := (good s).sub ((good R.quiet).mul_const _)
  have entry (s:R.Mode) : (charge μ Z-(charge μ Z).part R.quiet • Q).part s=∫y,part s y ∂μ := by
    rw [Extra.Trajectories.part_sub,Poly.part_smul,components,components,
      ←integral_mul_const,←integral_sub (good s) ((good R.quiet).mul_const (Q.part s))]
  unfold Poly.price
  simp only [Extra.Trajectories.part_sub,Poly.part_smul]
  change (∑s,Poly.toll w s * ‖(charge μ Z).part s-(charge μ Z).part R.quiet*Q.part s‖) ≤
    ∫y, ∑s,Poly.toll w s * ‖part s y‖ ∂μ
  rw [integral_finsetSum _ (fun s _=>(paid s).norm.const_mul _)]
  apply sum_le_sum
  intro s _
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (Poly.worth hw _).le
  have h := entry s
  rw [Extra.Trajectories.part_sub,Poly.part_smul] at h
  rw [h]
  exact norm_integral_le_integral_norm _

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Rep G f} {O : ChartRatio G}
  (K : Bulk.Kernel S P.clip P.path O) (F : Forest S.ratio) (t : S.Choices)
  (g : ℝ) (x : fieldDir G c 1) (W : Bulk.Colors R G f)
  (D : Lit R (Config G f)) (w : I→ℝ) (Q : Poly R)

def calmBill (y : F.Slice G) : ℝ :=
  let U := F.drape y
  let b := weight g (levelScalar P) U W P.clip P.path
  let L := markedLog g U W
  let M := model g (levelScalar P) W K U
  taggedKernel S (temperature g) t U (sample g x) *
    (P.eval U * (Real.exp (Poly.price w L)*(Real.exp (mixedBill (P:=P) W D g w U)-1))+
      max (P.eval U) b * |remainderVac W U g P| * Poly.price w (unitScale M-Q))

/-- The incoming logarithmic fee is summed over every mixed sector at
the original weights. The physical vacuum perturbation is paid only
against the centered model field. -/
theorem represented_older (floor : Floor P D) (well : Bulk.Well W)
    (hw : ∀i,0<w i) (heat : P.beta=temperature g)
    (A : Set (F.Slice G)) (hA : MeasurableSet A) (inside : ∀y∈A,F.drape y∈Calm P.p)
    (boundOn : F.Slice G → ℝ) (finite : IntegrableOn boundOn A (F.order G))
    (majorant : ∀y∈A, calmBill K F t g x W D w Q y ≤ boundOn y) :
    let E := charge (F.order G) (older K F t g (levelScalar P) x W A D)
    Poly.price w (E-E.part R.quiet • Q) ≤ ∫y in A,boundOn y ∂F.order G := by
  intro E
  let raw := stack t (sample g x) (temperature g) (olderInput K g (levelScalar P) W D) ∘ F.drape
  have good : Good ((F.order G).restrict A) raw := (good_slice F t (sample g x) (temperature g)
    K.branches (leaf_sub floor.safe (leaf_model K g (levelScalar P) W well))).within A
  change Poly.price w (charge (F.order G) (A.indicator raw)-
    (charge (F.order G) (A.indicator raw)).part R.quiet • Q) ≤ _
  rw [←restricted_cost hA raw]
  apply (center_integral _ raw good Q w hw).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun _=>Poly.nonnegative hw _) finite
  filter_upwards [ae_restrict_mem hA] with y hy
  apply le_trans _ (majorant y hy)
  let U := F.drape y
  have calm : U∈Calm P.p := inside y hy
  have positive : 0<P.eval U := healthy_live calm
  have bound := tagged_center_price (D U) (model g (levelScalar P) W K U) Q w hw
    positive (show 0<weight g (levelScalar P) U W P.clip P.path from Real.exp_pos _)
    (kernel_nonneg (temperature g) t U (sample g x)) (floor.vacancy U) (model_unit ..)
  dsimp only at bound
  rw [calm_vacuum_change W g U heat calm,abs_neg] at bound
  apply bound.trans
  apply mul_le_mul_of_nonneg_left _ (kernel_nonneg ..)
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left (calm_mixed_change K W D g w floor hw U calm) positive.le

end YM.Integration.FVA1Physical.OlderPrice

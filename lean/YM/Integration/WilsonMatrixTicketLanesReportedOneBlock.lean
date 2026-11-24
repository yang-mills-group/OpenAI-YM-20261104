import YM.Integration.WilsonMatrixTicketLanesReportedPlatedBank
import YM.RGComparison.Core16.Spool.Proof

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedOneBlock
open Function Filter MeasureTheory FVA2 OPE RG12 RG17 Extraction Spec Wilson Table RG Lattice
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedPlating
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

/-- The actual paid block immediately below the reporting date. -/
def step {m b : ℕ} (p : ℕ) (atStage : m = b+1) : StepData (R.family.side b p) (R.family.side m p) :=
  atStage.symm ▸ R.family.path.levels.clock.op b p

private theorem certified {m b : ℕ} (p : ℕ) (atStage : m = b+1) (β : ℝ) :
    (step R p atStage).IsKernel β G := by
  subst m
  exact R.family.path.levels.transition_mass b p β

private theorem linear {c f : Side} (D : StepData c f) (β : ℝ) (h : D.IsKernel β G)
    (U : Config G c) {A : Type} [Fintype A]
    (z : A → ℂ) (X : A → Config G f → ℂ) (good : ∀ a,Integrable (X a) (prior G f)) :
    D.push β (fun V => ∑ a,z a * X a V) U = ∑ a,z a * D.push β (X a) U := by
  unfold RG.StepData.push
  simp only [Finset.smul_sum,Complex.real_smul]
  simp_rw [show ∀ V a,(D.density β V U:ℂ) * (z a * X a V) =
    z a * (D.density β V U * X a V) from fun _ _ => by ring]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro a _
    have t := StepData.push_slice h U (X a) (good a)
    simpa only [Complex.real_smul] using t.const_mul (z a)

/-- Evaluate the whole freshly registered nonlinear field on the actual one-step
compact Wilson kernel at the inherited temperature. The finite sum outside its
common normalized integral uses the same real cutoff cost as the full upper field. -/
theorem original {I : Type} [Fintype I] (r : ℝ) (d : I → ℕ) (w : ∀ i,R.family.label (d i))
    (b N p : ℕ) (atStage : L.level r = b+1) (age : ∀ i,R.family.ref (d i) ≤ L.level r)
    (future : L.level r ≤ N) (u : Directions G (R.family.side b p))
    (o : I → Site (R.family.side (L.level r) p)) :
    let m := L.level r
    let D := step R p atStage
    let g := regulatorRun R.family N p m
    let lamps (j : ∀ i,(R.family.labels.level (d i)).Index) := fun i => WilsonCoherentTerminalFrame.lamp R (d i) (j i)
    let x := fun i => atRef L (d i) r (N,p) (w i)
    (Spool.spinVac D u g)⁻¹ • D.push (g⁻¹^2) (fun V => bare (g⁻¹^2) V •
      (∏ i,R.family.O m p (center R m N p (x i)) (o i) V)) (Parcel.Oven.slice u g) =
    ∑ j : (∀ i,(R.family.labels.level (d i)).Index),
      (∏ i,WilsonMatrixTicketLanesReportedMaster.color R (d i) m N p (L.shift (d i) r (w i)) (j i)) *
      Spool.reads (lamps j) D u o g := by
  intro m D g lamps x
  let β := g⁻¹^2
  let dock := Parcel.Oven.slice u g
  let c (j : ∀ i,(R.family.labels.level (d i)).Index) := ∏ i,column R F L (d i) r (w i) (j i)
  let X (j : ∀ i,(R.family.labels.level (d i)).Index) := fun V : Config G (R.family.side m p) =>
    bare β V • Spool.tally (lamps j) o V
  have good j : Integrable (X j) (prior G (R.family.side m p)) :=
    ((bare_cont β).smul (Spool.tally_cont (lamps j) o)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have common : (fun V : Config G (R.family.side m p) => bare β V •
      (∏ i,R.family.O m p (center R m N p (x i)) (o i) V)) = fun V => ∑ j,c j * X j V := by
    funext V
    rw [WilsonMatrixTicketLanesReportedPlatedBank.joint R F L r d w N p age future o V,Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change bare β V • (c j * _) = c j * (bare β V • _)
    rw [Complex.real_smul,Complex.real_smul]
    unfold Spool.tally
    ring
  have moved := linear D β (certified R p atStage β) dock c X good
  change (Spool.spinVac D u g)⁻¹ • D.push β _ dock = _
  rw [common,moved,Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have pg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson future))
  rw [←WilsonMatrixTicketLanesReportedPlatedBank.normalized R F L r d w N p j]
  change (Spool.spinVac D u g)⁻¹ • (c j * Spool.survey (lamps j) D u o g) =
    (g:ℂ)^(Spool.power (lamps j)) * c j * (g⁻¹^(Spool.power (lamps j)) •
      ((Spool.spinVac D u g)⁻¹ • Spool.survey (lamps j) D u o g))
  simp only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv]
  have cancel : (g:ℂ)^(Spool.power (lamps j)) * ((g:ℂ)⁻¹)^(Spool.power (lamps j)) = 1 := by
    rw [←mul_pow,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr pg.ne'),one_pow]
  calc
    _ = ((g:ℂ)^(Spool.power (lamps j)) * ((g:ℂ)⁻¹)^(Spool.power (lamps j))) *
      ((Spool.spinVac D u g:ℂ)⁻¹ * (c j * Spool.survey (lamps j) D u o g)) := by
        rw [cancel,one_mul]
    _ = _ := by ring

end YM.Integration.WilsonMatrixTicketLanesReportedOneBlock

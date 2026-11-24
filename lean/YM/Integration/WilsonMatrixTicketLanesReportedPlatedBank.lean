import YM.Integration.WilsonMatrixTicketLanesReportedPlating

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedPlatedBank
open Filter FVA2 OPE RG12 RG17 Extraction Spec Wilson Table RG Lattice Labels Source RG16.Literal
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Astage
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedPlating
open WilsonTranslatedFactory Next.Rank.Price Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

/-- The primary in the exact original normalized cutoff credit has coefficients
fixed before either upper regulator. All the old signed components are retained. -/
theorem held (d : ℕ) (r : ℝ) (w : R.family.label d) (N p : ℕ)
    (age : R.family.ref d ≤ L.level r) (future : L.level r ≤ N)
    (o : Site (R.family.side (L.level r) p)) (U : Config G (R.family.side (L.level r) p)) :
    let m := L.level r
    let x := atRef L d r (N,p) w
    let Q := entry R.makes future o ((R.family.factory d N p).terminal.symm x)
    let Y := R.family.path.rep N p m
    credit R.family N p 0 (R.family.O N p x (Push.GridApprox.anchor R.family.S p future o)) m future U /
        (Y.eval U : ℂ) =
      (∑ j,column R F L d r w j * Light (WilsonCoherentTerminalFrame.lamp R d j)
        (R.family.side m p) o U) +
      ((R.family.S.a m : ℂ)^d)⁻¹ * WilsonMatrixTicketLanesReportedCredit.remainder R Q Y o U := by
  let v := WilsonMatrixTicketLanesReportedMaster.color R d (L.level r) N p (L.shift d r w)
  have claim := WilsonMatrixTicketLanesReportedCredit.held R age future o v U
  dsimp only at claim ⊢
  rw [show Axle.root R.makes d (L.level r) N p v = atRef L d r (N,p) w from
    WilsonMatrixTicketLanesReportedMaster.finite R F L d r w N p age future] at claim
  rw [claim,measured R F L d r w N p age future]

variable {I : Type} [Fintype I]

/-- The whole fresh product is a single finite signed expansion on the same
Wilson configuration, with the prescribed heterogeneous positions. -/
theorem joint (r : ℝ) (d : I → ℕ) (w : ∀ i,R.family.label (d i)) (N p : ℕ)
    (age : ∀ i,R.family.ref (d i) ≤ L.level r) (future : L.level r ≤ N)
    (o : I → Site (R.family.side (L.level r) p)) (U : Config G (R.family.side (L.level r) p)) :
    (∏ i,R.family.O (L.level r) p
      (center R (L.level r) N p (atRef L (d i) r (N,p) (w i))) (o i) U) =
      ∑ a : (∀ i,(R.family.labels.level (d i)).Index),
        (∏ i,column R F L (d i) r (w i) (a i)) *
        ∏ i,Light (WilsonCoherentTerminalFrame.lamp R (d i) (a i))
          (R.family.side (L.level r) p) (o i) U := by
  simp_rw [fun i => measured R F L (d i) r (w i) N p (age i) future (o i) U]
  simp [Finset.prod_univ_sum,Finset.prod_mul_distrib]

/-- The physical normalization of every actual angular leg is exactly the
compensated cutoff color, including its true regulator-dependent temperature. -/
theorem thermal (d : ℕ) (r : ℝ) (w : R.family.label d) (N p : ℕ)
    (j : (R.family.labels.level d).Index) :
    (regulatorRun R.family N p (L.level r) : ℂ)^((R.family.labels.level d).grades j).2 *
      column R F L d r w j =
    WilsonMatrixTicketLanesReportedMaster.color R d (L.level r) N p (L.shift d r w) j := by
  unfold WilsonMatrixTicketLanesReportedPlating.column WilsonMatrixTicketLanesReportedMaster.color
  simp only [Labels.Frame.scaled_apply,Complex.ofReal_pow]
  change (_ : ℂ)^_ * (_^_ * _) = (((regulatorRun R.family N p (L.level r) /
    R.family.path.levels.clock.threshold (L.level r):ℝ):ℂ)^_ * _)
  rw [Complex.ofReal_div,div_eq_mul_inv,mul_pow,Complex.ofReal_inv,mul_assoc]

/-- One signed unit conversion for the entire heterogeneous normalized Spool
word, using its actual microscopic Taylor grade. -/
theorem normalized (r : ℝ) (d : I → ℕ) (w : ∀ i,R.family.label (d i)) (N p : ℕ)
    (a : ∀ i,(R.family.labels.level (d i)).Index) :
    (regulatorRun R.family N p (L.level r) : ℂ)^
        Spool.power (fun i => WilsonCoherentTerminalFrame.lamp R (d i) (a i)) *
      (∏ i,column R F L (d i) r (w i) (a i)) =
      ∏ i,WilsonMatrixTicketLanesReportedMaster.color R (d i) (L.level r) N p
        (L.shift (d i) r (w i)) (a i) := by
  change (_:ℂ)^(∑ i,((R.family.labels.level (d i)).grades (a i)).2) * _ = _
  simp_rw [←fun i=>thermal R F L (d i) r (w i) N p (a i)]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

private theorem single (d : ℕ) (r : ℝ) (w : R.family.label d) (N p : ℕ) (future : L.level r ≤ N) :
    mass R.family d (WilsonMatrixTicketLanesReportedMaster.color R d (L.level r) N p (L.shift d r w)) ≤
      (2:ℝ)^d * mass R.family d (L.shift d r w) := by
  let t := shrink R.family (L.level r) N p
  have pos : 0 ≤ t := (shrink_pos R.family R.makes future p).le
  have bound : t ≤ 2 := RG12.Arche.shrink_current (C:=R.family) (p:=p) R.makes future
  unfold mass Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖(R.family.labels.level d).scaled t (L.shift d r w) i‖ ≤ _
  rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg pos _)]
  exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ pos bound _).trans
    (pow_le_pow_right₀ one_le_two (Planned.PrimaryIntegral295.Film.second_fits (R.family.labels.level d) i)))
    (norm_nonneg _)

/-- Total absolute charge of the compensated columns, before all upper cutoffs
and torus periods, including all choices of physical angular colors. -/
theorem cost (r : ℝ) (d : I → ℕ) (w : ∀ i,R.family.label (d i)) (N p : ℕ) (future : L.level r ≤ N) :
    (∑ a : (∀ i,(R.family.labels.level (d i)).Index),
      ‖∏ i,WilsonMatrixTicketLanesReportedMaster.color R (d i) (L.level r) N p
        (L.shift (d i) r (w i)) (a i)‖) ≤
      ∏ i,(2:ℝ)^(d i)*mass R.family (d i) (L.shift (d i) r (w i)) := by
  calc
    _ = ∏ i,mass R.family (d i) (WilsonMatrixTicketLanesReportedMaster.color R (d i)
        (L.level r) N p (L.shift (d i) r (w i))) := by
      simp [mass,Labels.Frame.coeffSize,Finset.prod_univ_sum]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => mass_nonneg ..)
      (fun i _ => single R F L (d i) r (w i) N p future)

end YM.Integration.WilsonMatrixTicketLanesReportedPlatedBank

import YM.Integration.WilsonMatrixTicketLanesRegulatorColumn
import YM.Integration.WilsonMatrixTicketLanesReportedAccuracy

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegulatorCoupon
open Filter Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedOneBlock
open WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesRegulatorColumn
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

def fresh {n b k : ℕ} (d : Fin n → ℕ) (N p : ℕ) (top : ∀i,R.family.label (d i))
    (stage : k=b+1) (u : Pins G (R.family.side b p)) (o : Fin n → Site (R.family.side k p)) : ℂ :=
  let g := regulatorRun R.family N p k
  let D := step R p stage
  (Spool.spinVac D u g)⁻¹ • D.push (g⁻¹^2) (fun V => bare (g⁻¹^2) V •
    ∏i,R.family.O k p (center R k N p (top i)) (o i) V) (Parcel.Oven.slice u g)

def forecast {I : Type} [Fintype I] {k : ℕ} (d : I → ℕ) (N p : ℕ) (top : ∀i,R.family.label (d i))
    (v : (∀ i,(R.family.labels.level (d i)).Index) → ℂ) : ℂ :=
  ∑ j,(∏i,WilsonMatrixTicketLanesReportedMaster.color R (d i) k N p
    (entry R (d i) k N p (top i)) (j i))*v j

include L in
/-- Common finite-torus Taylor coupon for any prescribed actual upper operators
at any late reporting date. Their cutoff-dependent normalized quotas carry all
angular and engineering costs. -/
theorem original (simple : G.Simple) (paid : Paid G R.kit) {n : ℕ} (d : Fin n → ℕ) (s cap : ℕ) :
    ∀ᶠ b : ℕ in atTop,∀ (k N p : ℕ) (stage : k=b+1), k≤N → (∀i,R.family.ref (d i)≤k) →
      ∀ (top : ∀i,R.family.label (d i)) (large : Bid.Larger (G:=G) (step R p stage))
        (T : Forest (step R p stage).ratio) (u : Pins G (R.family.side b p))
        (o : Fin n → Site (R.family.side k p)) (tag : (step R p stage).Choices)
        (v : (Descent.nil (top:=R.family.side k p)).Tags), (∀j,‖u j‖≤(cap:ℝ)+1) →
        ‖fresh R d N p top stage u o - forecast R (k:=k) d N p top
          (WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d s stage large T u o tag v)‖ ≤
          (∏i,(2:ℝ)^(d i)*((R.family.S.a k^(d i))⁻¹*Next.UVStress.quota R.family (d i) k N p (top i))) *
            (regulatorRun R.family N p k^(s+1)*(2+Real.log (R.family.path.levels.clock.hatBeta b))) := by
  filter_upwards [WilsonMatrixTicketLanesReportedCoupon.original R simple paid d s cap] with b rows
  intro k N p stage future age top large T u o tag v inside
  let Y := dated R F L k
  let w i := entry R (d i) k N p (top i)
  have row := rows F Y 0 stage w age N p future large T u o tag v inside
  have physical i : atRef Y (d i) 0 (N,p) (w i) = top i := attached R F L (d i) k N p (age i) future (top i)
  have costs i : mass R.family (d i) (Y.shift (d i) 0 (w i)) =
      (R.family.S.a k^(d i))⁻¹*Next.UVStress.quota R.family (d i) k N p (top i) :=
    cost R F L (d i) k N p (age i) future (top i)
  have observed : WilsonMatrixTicketLanesReportedSettlement.fresh R F Y 0 d w b N p stage u o =
      fresh R d N p top stage u o := by
    unfold WilsonMatrixTicketLanesReportedSettlement.fresh fresh
    dsimp only
    simp_rw [physical]
    rfl
  have signed (field : (∀i,(R.family.labels.level (d i)).Index) → ℂ) : WilsonMatrixTicketLanesReportedSettlement.priced R F Y 0 d w N p field =
      forecast R (k:=k) d N p top field := rfl
  rw [observed,signed] at row
  simp only [costs] at row
  dsimp only [Y,dated] at row
  exact row

include L in
/-- With a polynomial quota at the true intervening stage the genuine numerical
remainder costs any desired power of its own inherited coupling. -/
theorem billed (simple : G.Simple) (paid : Paid G R.kit) {n : ℕ} (d e : Fin n → ℕ)
    (q cap : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ b : ℕ in atTop,∀ (k N p : ℕ) (stage : k=b+1),k≤N → (∀i,R.family.ref (d i)≤k) →
      ∀ (top : ∀i,R.family.label (d i)) (amount : Fin n→ℝ),
      (∀i,(R.family.S.a k^(d i))⁻¹*Next.UVStress.quota R.family (d i) k N p (top i) ≤
        R.family.path.levels.clock.hatBeta k^(e i)*amount i) → (∀i,0≤amount i) →
      ∀ (large : Bid.Larger (G:=G) (step R p stage)) (T : Forest (step R p stage).ratio)
        (u : Pins G (R.family.side b p)) (o : Fin n → Site (R.family.side k p)) (tag : (step R p stage).Choices)
        (v : (Descent.nil (top:=R.family.side k p)).Tags), (∀j,‖u j‖≤(cap:ℝ)+1) →
        ‖fresh R d N p top stage u o - forecast R (k:=k) d N p top
          (WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d (q+2*((∑i,e i)+1)) stage large T u o tag v)‖ ≤
          ε*regulatorRun R.family N p k^q*∏i,amount i := by
  let h := ∑i,e i
  let A := ∏i,(2:ℝ)^(d i)
  have growing : Tendsto (fun b : ℕ=>b+1) atTop atTop :=
    tendsto_atTop.2 (fun k=>(eventually_ge_atTop k).mono fun b h=>by omega)
  have rates := growing.eventually (WilsonMatrixTicketLanesReportedAccuracy.coupon R simple q h A ε
    (Finset.prod_nonneg fun _ _=>by positivity) positive)
  filter_upwards [original R F L simple paid d (q+2*(h+1)) cap,rates] with b rows rate
  intro k N p stage future age top amount bank pos large T u o tag v inside
  have cash := rows k N p stage future age top large T u o tag v inside
  subst k
  let B := R.family.path.levels.clock.hatBeta (b+1)
  let g := regulatorRun R.family N p (b+1)
  let rent := g^(q+2*(h+1)+1)*(2+Real.log (R.family.path.levels.clock.hatBeta b))
  have rp : 0 ≤ rent := mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    (add_nonneg zero_le_two (Real.log_nonneg (R.family.path.levels.fits.delayed b).le))
  have lease := rate b N p (by omega) future
  calc
    _ ≤ _ := cash
    _ ≤ (∏i,(2:ℝ)^(d i)*(B^(e i)*amount i))*rent := by
      apply mul_le_mul_of_nonneg_right _ rp
      exact Finset.prod_le_prod (fun i _=>mul_nonneg (by positivity)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg (R.family.S.a_pos _).le _))
          (by rw [RG12.quota_charts R.family R.makes (d i) (b+1) (N,p) (age i) future]; exact mass_nonneg ..)))
        (fun i _=>mul_le_mul_of_nonneg_left (bank i) (by positivity))
    _ = (A*B^h*rent)*(∏i,amount i) := by
      dsimp only [A,h]
      simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right lease (Finset.prod_nonneg fun i _=>pos i)

end YM.Integration.WilsonMatrixTicketLanesRegulatorCoupon

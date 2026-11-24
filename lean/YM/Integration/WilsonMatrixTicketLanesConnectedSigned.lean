import YM.Integration.WilsonMatrixTicketLanesConnectedWeighted
import YM.Integration.WilsonMatrixOriginalMatchedForest

/-! The signed original spatial test of two moving deposited fields, including its two upper singleton means. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedSigned
open Function Filter Finset MeasureTheory Real Lattice Gauge RG Wilson Tree Precision Source Marker Extraction Spec
open RG12 RG17 FullVolume Extraction.Order Table Climb Trace.Pilot Next.UVStress PhysicalNext.Repeat.Legato Pert.Asymptotics
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel PhysMS
open WilsonMatrixTicketLanesConnectedBudget WilsonMatrixTicketLanesConnectedWeighted WilsonMatrixTicketLanesConnectedColumns
open WilsonMatrixTicketLanesReportedOneBlock WilsonInvariantActionSeparatedCells
open private volume_bill from YM.Integration.WilsonInvariantActionPromotedPair
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) (L : RG17.Layout F)
local notation "β" => R.family.path.levels.clock.hatBeta

def tested (d h : ℕ) (a : ℝ→R.family.label d) (c : ℝ→R.family.label h) {r : ℝ} (hr : 0<r)
    (φ : Test 2) {b N p : ℕ} (date : L.level r=b+1) (future : L.level r ≤ N) (u : Directions G (R.family.side b p)) : ℂ :=
  ∑x:Fin 2→Site (R.family.side N p),WilsonExternalMeshMass.charge R.family (dilate hr φ) x *
    let o:=fun i=>(R.family.S.toDepth future p).parent (x i)
    joint R F L r d h (a r) (c r) b N p date u (o 0) (o 1)-single R F L r d (a r) b N p date u (o 0)*single R F L r h (c r) b N p date u (o 1)

def Negligible (U : Filter (ℕ×ℕ)) (d h : ℕ) (g : ℝ→ℝ) (a : ℝ→R.family.label d) (c : ℝ→R.family.label h) (φ : Test 2) : Prop :=
  ∀ q cap : ℕ,∀ ε>0,∀ᶠ r in trail,∀hr:0<r,∀ᶠ z:ℕ×ℕ in U,∃ b,∃ date:L.level r=b+1,∃ future:L.level r<z.1,
    ∀ u : Directions G (R.family.side b z.2), (∀i,‖u i‖ ≤ (cap:ℝ)+1) →
      ‖tested R F L d h a c hr φ date (p:=z.2) future.le u‖ ≤ ε*(g r)^q

private theorem larger {m b p : ℕ} (date : m=b+1) (large : Bid.Larger (G:=G) (R.family.path.levels.clock.op b p)) :
    Bid.Larger (G:=G) (step R p date):=by subst m;exact large

/-- Both honest engineering charges are added before choosing the Wick order. The signed spatial mass is on the prescribed original cutoff filter. -/
theorem purchased (simple : G.Simple) (paid : Paid G R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (large : 17 ≤ B) (level : L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {U : Filter (ℕ×ℕ)} (chosen : U ≤ L.lens) (d h : ℕ) (g : ℝ→ℝ) (coupling : Coupling G g)
    (a : ℝ→R.family.label d) (c : ℝ→R.family.label h) (φ : Test 2) (e s : ℕ) (D E : ℝ)
    (D₀ : 0 ≤ D) (E₀ : 0 ≤ E)
    (first : ∀ᶠ r in trail,mass R.family d (L.shift d r (a r)) ≤ D*β (L.level r)^e)
    (second : ∀ᶠ r in trail,mass R.family h (L.shift h r (c r)) ≤ E*β (L.level r)^s) : Negligible R F L U d h g a c φ:=by
  intro q cap ε ep
  let M:ℝ:=(∫ x,‖φ x‖)+1
  let C:ℝ:=M*(2:ℝ)^d*D*(2:ℝ)^h*E
  have Mp:0 ≤ M:=by dsimp only [M];positivity
  have Cp:0 ≤ C:=by dsimp only [C];positivity
  let t:=q+2*((e+s)+1)+1
  have one:0<(1:ℝ):=one_pos
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B (by omega)
  have old:Tendsto (fun r=>L.level r-1) trail atTop:=tendsto_atTop.2 fun i=>(grow.eventually_ge_atTop (i+1)).mono fun r hr=>by change i ≤ L.level r-1;omega
  have enough:=grow.eventually (WilsonMatrixTicketLanesReportedAccuracy.coupon R simple q (e+s) C (ε/2^q) Cp (div_pos ep (pow_pos zero_lt_two _)))
  have clock:=WilsonPhysicalCutoffCurrency.band R simple pace (B:=B) (by omega) g coupling
  filter_upwards [WilsonMatrixTicketLanesConnectedWeighted.plated R F L simple paid pace large level d h t cap φ 1 one,
    first,second,enough,old.eventually (MatchingR2.Top.step_shape R.family.path),grow.eventually_ge_atTop 1, clock]
    with r rows aCost cCost tail allForests hot band
  intro hr
  let m:=L.level r
  let b:=m-1
  have date:m=b+1:=by dsimp only [m,b] at *;omega
  have later:∀ᶠz:ℕ×ℕ in f.fuse,m<z.1:=by
    change ∀ᶠ_:ℕ in atTop,∀ᶠ j:ℕ in atTop,m<f.mesh j
    exact .of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop m
  let ψ:=dilate hr φ
  have massTest:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport one).filter_mono (chosen.trans L.certified)
  filter_upwards [later.filter_mono (chosen.trans L.certified),massTest] with z future massBound
  refine ⟨b,date,future,?_⟩
  intro u pin
  let K:=step R z.2 date
  obtain ⟨T⟩:=Tree.select K.ratio K.patch.odd_side
  let largeK:=larger R date (allForests z.2)
  let g₀:=regulatorRun R.family z.1 z.2 m
  let fee:=amount R F L d r (a r)*amount R F L h r (c r)*g₀^t
  let charge (x:Fin 2→Site (R.family.side z.1 z.2)):=WilsonExternalMeshMass.charge R.family ψ x
  let cov (x:Fin 2→Site (R.family.side z.1 z.2)):=
    let o:=fun i=>(R.family.S.toDepth future.le z.2).parent (x i)
    joint R F L r d h (a r) (c r) b z.1 z.2 date u (o 0) (o 1)-single R F L r d (a r) b z.1 z.2 date u (o 0)*single R F L r h (c r) b z.1 z.2 date u (o 1)
  have gx:0 ≤ g₀:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have positive (k : ℕ) (w : R.family.label k) : 0 ≤ amount R F L k r w:=
    mul_nonneg (pow_nonneg zero_le_two _) (RG12.mass_nonneg R.family _ _)
  have weight:0 ≤ fee:=mul_nonneg (mul_nonneg (positive _ _) (positive _ _)) (pow_nonneg gx _)
  have each x : ‖charge x*cov x‖ ≤ ‖charge x‖*fee:=by
    by_cases blank:charge x=0
    · simp [blank]
    · rw [norm_mul];apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [one_mul] using rows b date hr (a r) (c r) z.1 z.2 future.le x blank T largeK u pin
  have budget:∑x,‖charge x‖ ≤ M:=by simpa only [charge,M,ψ,volume_bill] using massBound
  have βp:0<β m:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have Dm:1 ≤ 2+log (β m):=by linarith only [Real.log_nonneg (R.family.path.levels.fits.delayed m).le]
  have coarse:g₀ ≤ 2*g r:=by simpa only [g₀,m,level] using (band z.1 z.2 (by simpa only [m,level] using future.le)).2
  have costs:amount R F L d r (a r)*amount R F L h r (c r) ≤ ((2:ℝ)^d*(D*β m^e))*((2:ℝ)^h*(E*β m^s)):=
    mul_le_mul (mul_le_mul_of_nonneg_left aCost (pow_nonneg zero_le_two _))
      (mul_le_mul_of_nonneg_left cCost (pow_nonneg zero_le_two _)) (positive _ _)
      (mul_nonneg (pow_nonneg zero_le_two _) (mul_nonneg D₀ (pow_nonneg βp.le _)))
  have finance:M*fee ≤ C*β m^(e+s)*g₀^t:=by
    calc
      _ ≤ M*((((2:ℝ)^d*(D*β m^e))*((2:ℝ)^h*(E*β m^s)))*g₀^t):=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right costs (pow_nonneg gx _)) Mp
      _ = _:=by dsimp only [C];rw [pow_add];ring
  have edge:=tail m z.1 z.2 le_rfl future.le
  have fare:C*β m^(e+s)*g₀^t ≤ ε/2^q*g₀^q:=
    (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (pow_nonneg gx t) Dm) (mul_nonneg Cp (pow_nonneg βp.le (e+s)))).trans edge
  change ‖∑x,charge x*cov x‖ ≤ _
  calc
    _ ≤ ∑x,‖charge x*cov x‖:=norm_sum_le _ _
    _ ≤ ∑x,‖charge x‖*fee:=Finset.sum_le_sum fun x _=>each x
    _ ≤ M*fee:=(Finset.sum_mul ..).symm.le.trans (mul_le_mul_of_nonneg_right budget weight)
    _ ≤ ε/2^q*g₀^q:=finance.trans fare
    _ ≤ ε/2^q*(2*g r)^q:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gx coarse q) (div_nonneg ep.le (pow_nonneg zero_le_two _))
    _ = _:=by rw [mul_pow];field_simp

end YM.Integration.WilsonMatrixTicketLanesConnectedSigned

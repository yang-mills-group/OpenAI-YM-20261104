import YM.Integration.WilsonPhysicalHistoryRetainedSpringBareSite

/-! The independently issued earlier finite program on the measured angular
field. Each original site bears the complete kinetic and signed packet term. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice Laurent Bloch Wilson RG Precision Exterior Tree PowerSeries Marker MeasureTheory
open IterationFour IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge}

def finitePitch (R : Run G) (N j r : ℕ) (g : ℝ) : ℝ := 1+g^2*pitchPolynomial R N j r g

def springAt (R : Run G) (N n j r : ℕ) (Z : SeriesA G) (g : ℝ)
    (x : Site (R.family.side j n)) (U : Config G (R.family.side j n)) : ℝ :=
  let B:=(R.family.path.levels.params j).clip
  let K:=(R.family.path.rep N n j).path
  let p:=finitePitch R N j r g
  g^2*pitchTail R N j r g*(secondAt B K x U+interactionAt K x U)+
    R.alloy.B.kin.alpha N j*interactionAt K x U+
      (Integral.temperature g*p)*springPacketsAt Z (g/Real.sqrt p) x U

def springSiteBill (R : Run G) (N j r : ℕ) (Z : SeriesA G) (g b : ℝ) : ℝ :=
  let D:=R.family.path.levels.params j
  let p:=finitePitch R N j r g
  |g^2*pitchTail R N j r g| * (quadraticBill D.clip D.paths+24*D.paths)+
    |R.alloy.B.kin.alpha N j| * (24*D.paths)+
      |Integral.temperature g*p| * packetBill Z (g/Real.sqrt p) b

theorem filed_sites {V : Type} [DecidableEq V] {Γ : Census V}
    (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    {d : LocalFormal.Datum R.family Γ} (F : FundedSpringFineInlet.Inlet J A d)
    (Z : SeriesA G) {σ b : ℝ} (D : RunFundedPeriodAction.PeriodData Z J.order σ b)
    (g : ℝ) (U : Config G (R.family.side d.level d.period)) :
    springReading R (FundedSpringPeriodPlan.plan R F Z σ b D) d.level g U=
      ∑ x : Site (R.family.side d.level d.period),springAt R d.cutoff d.period d.level J.order Z g x U := by
  obtain ⟨_,hi,hm⟩:=bare_sites (R.family.path.levels.params d.level).clip (R.family.path.rep d.cutoff d.period d.level).path U
  rw [filed_previous R F Z D,hm,hi,period_sites]
  simp only [springAt,Finset.sum_add_distrib,Finset.mul_sum,mul_add]
  rfl

theorem filed_site_price (R : Run G) (N n j r : ℕ) (accepted : j≤N)
    (Z : SeriesA G) {σ b : ℝ} (hs : 0<σ) (paid : Draw Z σ b) (g : ℝ)
    (x : Site (R.family.side j n)) :
    Measurable (springAt R N n j r Z g x) ∧
      ∀ U,‖springAt R N n j r Z g x U‖ ≤ springSiteBill R N j r Z g b := by
  let D:=R.family.path.levels.params j
  let K:=(R.family.path.rep N n j).path
  have h : R.family.path.Conv N n j:=R.makes.wilson.represents N n j accepted
  have paths : K.Bounds D.clip D.width D.paths (R.family.path.levels.clock.loopCap j) := by
    dsimp only [D,K]
    rw [←h.clip]
    exact h.good.paths
  obtain ⟨sm,sb,im,ib⟩:=bare_site_price paths x
  obtain ⟨zm,zb⟩:=period_site_price hs Z paid (g/Real.sqrt (finitePitch R N j r g)) x
  refine ⟨((measurable_const.mul (sm.add im)).add (measurable_const.mul im)).add (measurable_const.mul zm),?_⟩
  intro U
  unfold springAt springSiteBill
  dsimp only
  apply (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans ?_) ?_)
  · simp only [norm_mul,Real.norm_eq_abs]
    rw [←abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add (sb U) (ib U))) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (ib U) (abs_nonneg _))
  · rw [norm_mul,Real.norm_eq_abs (Integral.temperature _ * _)]
    exact mul_le_mul_of_nonneg_left (zb U) (abs_nonneg _)

end YM.Integration.OriginalMarkedRunAction

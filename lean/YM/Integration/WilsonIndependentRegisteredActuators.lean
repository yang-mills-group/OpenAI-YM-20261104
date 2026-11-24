import YM.Integration.WilsonIndependentRegisteredThermalRatios
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentRegisteredActuators
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics PhysicalNext.Repeat.Legato Next.Rank.Price
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonLimitConstruction
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "g" => regulatorRun R.family
local notation "θ" => (A).clock.threshold

private lemma reverse (hg:G.Simple){N m p:ℕ}(live:m<N):
    g N p (m+1) ≤ 2*g N p m :=by
  let b:=R.family.path.β N p m
  let c:=R.family.path.β N p (m+1)
  have paidR:b≤2*(A).clock.hatBeta m := (R.makes.wilson.represents N p m live.le).band.2
  have paidS:(A).clock.hatBeta (m+1)/2≤c := (R.makes.wilson.represents N p (m+1) live).band.1
  have mono:=WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos hg).le (Nat.le_succ m)
  have bp:0<b:=Overlay.beta_positive R.makes.wilson live.le
  have cp:0<c:=Overlay.beta_positive R.makes.wilson live
  have sq:Real.sqrt b ≤ 2*Real.sqrt c :=(Real.sqrt_le_left (by positivity)).2 (by nlinarith only [paidR,paidS,mono,Real.sq_sqrt cp.le])
  change (Real.sqrt c)⁻¹≤2*(Real.sqrt b)⁻¹
  rw [←one_div,←div_eq_mul_inv]
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr cp) (Real.sqrt_pos.mpr bp)).2 (by simpa using sq)

/-- Both actuator ratios are paid on the genuine cutoff-dependent coupling,
uniformly for every period and every original cutoff above this one edge. -/
theorem original (hg:G.Simple): ∀ᶠ m:ℕ in atTop,
    θ m/θ (m+1) ≤ 2 ∧ θ (m+1)/θ m ≤ 2 ∧
    ∀ N p:ℕ,m<N → shrink R.family m N p ≤ 6*shrink R.family (m+1) N p ∧
      shrink R.family (m+1) N p ≤ 4*shrink R.family m N p :=by
  filter_upwards [WilsonIndependentRegisteredThermalRatios.appointed R hg,WilsonVacuumPreResetSameTime.ratios R hg] with m head fee
  have hot : 0 < θ m := ((A).budget m).threshold_pos
  have next : 0 < θ (m+1) := ((A).budget (m+1)).threshold_pos
  refine ⟨(div_le_iff₀ next).mpr head.1,(div_le_iff₀ hot).mpr head.2,?_⟩
  intro N p live
  have funded:=fee N p live
  have other:=reverse R hg (p:=p) live
  have bp:=IterationFour.Currency.g_pos R.makes N p m live.le
  have cp:=IterationFour.Currency.g_pos R.makes N p (m+1) live
  change g N p m/θ m ≤ 6*(g N p (m+1)/θ (m+1)) ∧
    g N p (m+1)/θ (m+1) ≤ 4*(g N p m/θ m)
  rw [←mul_div_assoc,←mul_div_assoc,div_le_div_iff₀ hot next,div_le_div_iff₀ next hot]
  exact ⟨(mul_le_mul funded head.2 next.le (by positivity)).trans_eq (by ring),
    (mul_le_mul other head.1 hot.le (by positivity)).trans_eq (by ring)⟩

end YM.Integration.WilsonIndependentRegisteredActuators

import YM.Integration.WilsonPhysicalHistoryRetainedSpringClock

/-! On a cofinal common calendar the true finite regrading has a positive
radicand uniformly in every later cutoff and every torus. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice Wilson RG Precision Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Physical WilsonLimitConstruction PowerSeries
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem cofinal_temperature (R : Run G) (simple : G.Simple) (v : ℕ→Gear G→ℝ)
    (rows : FundedMarkedCoverRows.prices v R.kit) (r : ℕ) :
    ∃ T : Credit, ∀ᶠ j : ℕ in atTop, ∀ N>j,∀ n : ℕ,
      let g:=Pert.Asymptotics.regulatorRun R.family N n j
      let p:=finitePitch R N j r g
      |R.alloy.B.kin.alpha N j| ≤ T.buy (zz R.family.path.levels j) ∧
      |g^2*pitchTail R N j r g| ≤ 1/2 ∧ 1/2 ≤ p ∧ p ≤ 3/2 ∧
      |g/Real.sqrt p| ≤ 1 ∧ |Integral.temperature g*p| ≤ 3*R.family.path.levels.clock.hatBeta j := by
  obtain ⟨T,paid⟩:=cofinal_pitch R simple v rows (r+2)
  let w : ℝ:=((r-2+1:ℕ):ℝ)
  have one : 1≤w:=by
    change (1:ℝ) ≤ ((r-2+1:ℕ):ℝ)
    exact_mod_cast (show 1≤r-2+1 by omega)
  have pw : 0<w:=zero_lt_one.trans_le one
  refine ⟨T,?_⟩
  filter_upwards [paid,exp_at_band T R.family.path.levels simple 1 zero_lt_one,
    IterationFour.Currency.g_small simple R.makes (1/(2*w)) (by positivity)] with j credit cash small
  intro N later n
  let g:=Pert.Asymptotics.regulatorRun R.family N n j
  let C:=T.buy (zz R.family.path.levels j)
  let p:=finitePitch R N j r g
  let β:=R.family.path.β N n j
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N n j later.le
  have band:= (R.makes.wilson.represents N n j later.le).band
  have warm : 0<β:=Overlay.beta_positive R.makes.wilson later.le
  have hn : g*(2*w)<1:=(lt_div_iff₀ (by positivity)).1 (small N n later.le)
  have hw : g*w ≤ 1/2:=by linarith
  have half : g ≤ 1/2:=(le_mul_of_one_le_right gp.le one).trans hw
  have cb : C≤g⁻¹:=by
    have h:=cash β band.1
    change Real.exp C≤g^(-(1:ℝ)) at h
    rw [Real.rpow_neg_one] at h
    exact (by linarith [Real.add_one_le_exp C] : C ≤ Real.exp C).trans h
  have unit : g*C ≤ 1 := (mul_le_mul_of_nonneg_left cb gp.le).trans_eq (mul_inv_cancel₀ gp.ne')
  have hcost:=poly_price R N j r (by rw [abs_of_nonneg gp.le];linarith) (credit N later)
  have scaled (t : ℝ) (h : |t| ≤ w*C) : |g^2*t| ≤ 1/2 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg g)]
    calc
      _ ≤ g^2*(w*C) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = (g*w)*(g*C) := by ring
      _ ≤ (g*w)*1 := mul_le_mul_of_nonneg_left unit (mul_nonneg gp.le pw.le)
      _ ≤ 1/2 := by simpa only [mul_one] using hw
  have bounds:=abs_le.mp (scaled _ hcost.1)
  have lo : 1/2 ≤ p:=by dsimp only [p,finitePitch];linarith [bounds.1]
  have hi : p ≤ 3/2:=by dsimp only [p,finitePitch];linarith [bounds.2]
  have ph : 0<p:=by linarith
  have angle : |g/Real.sqrt p|≤1 := by
    rw [abs_of_nonneg (div_nonneg gp.le (Real.sqrt_nonneg _))]
    apply (div_le_one (Real.sqrt_pos.mpr ph)).2
    exact half.trans (Real.le_sqrt_of_sq_le (by nlinarith : (1/2:ℝ)^2 ≤ p))
  have temp : Integral.temperature g=β := by
    simp only [Integral.temperature,g,Pert.Asymptotics.regulatorRun,inv_pow,inv_inv]
    exact Real.sq_sqrt warm.le
  have head : coeff 2 (pitch R.family.path.levels R.metals.O N j)=R.alloy.B.kin.alpha N j :=
    (alpha_stable simple R.alloy.B.ratio R.alloy.B.support later.le).2 later
  refine ⟨head ▸ credit N later 2 (by omega),scaled _ hcost.2,lo,hi,angle,?_⟩
  change |Integral.temperature g*p| ≤ _
  rw [temp,abs_of_nonneg (mul_nonneg warm.le ph.le)]
  have hβ : β≤2*R.family.path.levels.clock.hatBeta j:=band.2
  calc
    β*p ≤ β*(3/2) := mul_le_mul_of_nonneg_left hi warm.le
    _ ≤ (2*R.family.path.levels.clock.hatBeta j)*(3/2) := mul_le_mul_of_nonneg_right hβ (by norm_num)
    _ = _ := by ring

end YM.Integration.OriginalMarkedRunAction

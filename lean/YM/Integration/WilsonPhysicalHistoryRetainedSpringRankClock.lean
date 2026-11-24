import YM.Integration.WilsonPhysicalHistoryRetainedSpringRankPrice
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMomentOrder

/-! The coefficient prices of finitely many angular ranks can all be paid
at the same date and coupling before choosing the physical period. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Finset Lattice RG Push Pressure Wilson Next.Fluctuations Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Physical PhysicalNext.Repeat.Legato WilsonLimitConstruction
open scoped BigOperators Topology Classical
variable {G : Gauge}

theorem cofinal_rank_factor (R : Run G) (simple : G.Simple) (k : ℕ) (C : ℝ) (hc : 0≤C)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N per : ℕ,m<N →
      let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
      C*(Real.exp (zz V (m+1)))^k≤ε*g^(-η) := by
  intro V
  let A:=C/ε
  have a0 : 0≤A:=div_nonneg hc ep.le
  let H : Credit:=⟨1,1+A+(k:ℝ),by linarith [Nat.cast_nonneg (α:=ℝ) k]⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (exp_at_band H V simple η hp),
    (tendsto_add_atTop_nat 1).eventually ((stamp_lim V simple).eventually_ge_atTop 1)]
    with m earned stage
  intro N per within g
  let z:=zz V (m+1)
  have cap:=earned (R.family.path.β N per (m+1)) (R.makes.wilson.represents N per (m+1) within).band.1
  have price : A*(Real.exp z)^k≤Real.exp (H.buy z):=by
    rw [←Real.exp_nat_mul]
    calc _≤Real.exp A*Real.exp ((k:ℝ)*z):=by gcongr;linarith [Real.add_one_le_exp A]
         _=Real.exp (A+(k:ℝ)*z):=(Real.exp_add ..).symm
         _≤_:=by
           apply Real.exp_le_exp.mpr
           change _≤(1+A+(k:ℝ))*z^1
           rw [pow_one]
           have big : 1≤z:=stage
           nlinarith [mul_nonneg a0 (sub_nonneg.mpr big)]
  calc _ = ε*(A*(Real.exp z)^k):=by dsimp only [A,z];field_simp
       _≤_:=mul_le_mul_of_nonneg_left (price.trans cap) ep.le

theorem cofinal_rank_unit (R : Run G) (simple : G.Simple) (h K s : ℕ) {ε η : ℝ}
    (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N per : ℕ,m<N →∀σ : ℝ,σ⁻¹≤Real.exp (zz V (m+1)) →
      let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
      (Real.exp (zz V (m+1)))^s*((max 1 σ⁻¹)^siteRankPower h K*siteRankPaper G h K)≤ε*g^(-η) := by
  intro V
  have paper : 0≤ siteRankPaper G h K:=sum_nonneg fun _ _=>abs_nonneg _
  filter_upwards [cofinal_rank_factor R simple (s+siteRankPower h K) _ paper ep hp,
    (tendsto_add_atTop_nat 1).eventually ((stamp_lim V simple).eventually_ge_atTop 1)]
    with m earn big
  intro N per future σ width g
  let z:=zz V (m+1)
  have z0 : 0≤z:=zero_le_one.trans big
  have v : max 1 σ⁻¹≤Real.exp z:=max_le (Real.one_le_exp z0) width
  have fit:=pow_le_pow_left₀ (zero_le_one.trans (le_max_left (1:ℝ) σ⁻¹)) v (siteRankPower h K)
  calc _≤(Real.exp z)^s*((Real.exp z)^siteRankPower h K*siteRankPaper G h K):=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right fit paper) (pow_nonneg (Real.exp_pos _).le _)
       _=siteRankPaper G h K*(Real.exp z)^(s+siteRankPower h K):=by rw [pow_add];ring
       _≤_:=earn N per future

theorem cofinal_path_scale (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,
      let D:=V.params (m+1)
      let z:=zz V (m+1)
      D.paths≤Real.exp z ∧ D.width⁻¹≤Real.exp z ∧ zz V (m+1)≤Real.exp z := by
  intro V
  filter_upwards with m
  let j:=m+1
  let z:=zz V j
  have logpos : 0<Real.log (V.clock.hatBeta j):=Real.log_pos (V.fits.delayed j)
  have logcap : Real.log (V.clock.hatBeta j)≤Real.exp z:=by
    rw [←Real.exp_log logpos];apply Real.exp_le_exp.mpr
    change Real.log (Real.log (V.clock.hatBeta j))≤1+Real.log (Real.log (V.clock.hatBeta j))
    linarith
  have stage : ActualRunAdmissionScales.profileCost V j≤Real.exp z:=calc
    _≤((V.S.block m).val:ℝ):=ActualRunAdmissionScales.profileCost_le_block V m
    _≤Real.log (V.clock.hatBeta m):=WilsonFundedMeasuredWindow.paced R slow m
    _≤Real.log (V.clock.hatBeta j):=Real.log_le_log (zero_lt_one.trans (V.fits.delayed m))
      (Push.Corrected.Last.band_le V simple (Nat.le_succ m))
    _≤_:=logcap
  have parts:=ActualRunAdmissionScales.profileCost_components V j
  exact ⟨parts.2.1.trans stage,parts.1.trans stage,by linarith [Real.add_one_le_exp z]⟩

end YM.Integration.OriginalMarkedRunAction

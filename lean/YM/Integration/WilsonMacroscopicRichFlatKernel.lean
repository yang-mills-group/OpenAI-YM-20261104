import YM.Push.BETA_TRANSPORT.Noise
import YM.FullVolume.Cross
import YM.OPE.Therm.Law
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFlatKernel
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox OPE OPE.Therm
open PhysicalNext.Repeat.Legato Push.BetaTransport Pressure
open scoped Classical Topology BigOperators
variable {G:Gauge}

/-- The cap at a fixed physical reference u, issued before all periods and cutoffs. -/
def rate (R:Run G)(u:ℕ):ℝ:=4*R.family.path.levels.clock.hatBeta (u+1)*R.family.path.levels.clock.kernel.penalty

def edges (R:Run G)(u per:ℕ):ℕ:=Fintype.card (Bond (R.family.side u per))

def front (R:Run G)(u N per:ℕ):ℝ:=Next.Fluctuations.Sector.prefactor (R.family.path.levels.clock.op u per) G (R.family.path.β N per (u+1))

private theorem noise {c f:Side}(S:StepData c f){β:ℝ}(b0:0≤β)(Q V:Config G c):
    let J:=Next.Fluctuations.Sector.prefactor S G β
    J*Real.exp (-(β*noiseCap S)) ≤ S.noise β Q V ∧ S.noise β Q V≤J:=by
  intro J;have J0:0≤J:=(pow_pos (inv_pos.mpr (S.penaltyZ_pos β (G:=G))) _).le
  have cost:=energy_estimate S Q
  have start:Real.exp (-(β*noiseCap S))≤Push.BetaTransport.Gibbs.factor (noiseEnergy S Q) β V:=by
    apply Real.exp_le_exp.mpr;nlinarith only [mul_le_mul_of_nonneg_left (cost.bound V) b0]
  have finish:Push.BetaTransport.Gibbs.factor (noiseEnergy S Q) β V≤1:=by
    apply Real.exp_le_one_iff.mpr;exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr b0) (cost.nonneg V)
  rw [noise_factor];exact ⟨mul_le_mul_of_nonneg_left start J0,(mul_le_mul_of_nonneg_left finish J0).trans_eq (mul_one J)⟩

/-- Actual last physical Wilson blocker, all fine and coarse configurations including the identity. The upper and lower prices share the same exact normalization and choice weights. -/
theorem purchased (R:Run G)(u per N:ℕ)(live:u+1≤N):
    0<front R u N per ∧ ∀(W:Config G (R.family.side (u+1) per))(V:Config G (R.family.side u per)),
      let K:=(R.family.path.levels.clock.op u per).density (R.family.path.β N per (u+1)) W V
      front R u N per*Real.exp (-(rate R u*(edges R u per:ℝ))) ≤ K ∧ K ≤ front R u N per:=by
  let H:=R.family.path;let S:=H.levels.clock.op u per;let β:=H.β N per (u+1);let J:=front R u N per
  have jp:0<J:=pow_pos (inv_pos.mpr (S.penaltyZ_pos β (G:=G))) _
  refine ⟨jp,?_⟩;intro W V K
  have band:=(R.makes.wilson.represents N per (u+1) live).band
  have b0:0≤β:=(div_nonneg (zero_lt_one.trans (H.levels.fits.delayed (u+1))).le (by norm_num:0≤(2:ℝ))).trans band.1
  have hot:β≤2*H.levels.clock.hatBeta (u+1):=band.2
  have ke:S.kernel.penalty=H.levels.clock.kernel.penalty:=rfl
  have cost:β*noiseCap S ≤ rate R u*(edges R u per:ℝ):=calc
    _≤(2*H.levels.clock.hatBeta (u+1))*noiseCap S:=mul_le_mul_of_nonneg_right hot (noiseCap_nonneg S)
    _=_:=by unfold noiseCap linkCap rate edges;rw [ke];ring
  let out:=J*Real.exp (-(rate R u*(edges R u per:ℝ)))
  have left (t:S.Choices):out≤S.noise β (S.prediction W t) V:=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg cost)) jp.le).trans (noise S b0 (S.prediction W t) V).1
  have right (t:S.Choices):S.noise β (S.prediction W t) V≤J:=(noise S b0 (S.prediction W t) V).2
  have chosen:(∑t:S.Choices,S.likelihood W t)=1:=S.chosen (H.levels.blocks u per).branches W
  constructor
  · calc
      out=∑t:S.Choices,S.likelihood W t*out:=by rw [←Finset.sum_mul,chosen,one_mul]
      _≤_:=Finset.sum_le_sum fun t _=>mul_le_mul_of_nonneg_left (left t) (S.likelihood_pos W t)
  · calc
      _≤∑t:S.Choices,S.likelihood W t*J:=Finset.sum_le_sum fun t _=>mul_le_mul_of_nonneg_left (right t) (S.likelihood_pos W t)
      _=J:=by rw [←Finset.sum_mul,chosen,one_mul]

end YM.Integration.WilsonMacroscopicRichFlatKernel


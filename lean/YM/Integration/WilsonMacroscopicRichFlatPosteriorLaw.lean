import YM.Integration.WilsonMacroscopicRichFlatFibre

/-! The complete finite Wilson law at one fixed lower configuration. Positivity
and normalization are preserved with every intervening Wilson link, so a
bounded interacting error can be integrated without a volume amplification. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw
open Filter Set MeasureTheory Lattice RG Wilson Source Extraction Push.GridApprox OPE OPE.Therm
open PhysicalNext.Repeat.Legato WilsonMacroscopicRichFlatFibre WilsonMacroscopicForwardTransfer
open scoped ENNReal Topology BigOperators
variable {G:Gauge} (R:Run G)

private theorem retained {u k:ℕ} (N per:ℕ) (uk:u+1≤k) (v:Config G (R.family.side u per)) :
    ∀W,∃a:ℝ,0≤a ∧ likelihood R N per uk v W=(a:ℂ) := by
  induction k,uk using Nat.le_induction with
  | base =>
    intro W
    refine ⟨raw R u N per v W,(R.family.path.levels.clock.op u per).density_positive _ W v,?_⟩
    simp only [likelihood,backTo_self,last]
  | succ k uk ih =>
    intro W
    let Z:=likelihood R N per uk v
    let S:=R.family.path.levels.clock.op k per
    let β:=R.family.path.β N per (k+1)
    have plotted (U):Z U=((Z U).re:ℂ) := by obtain ⟨a,_,ha⟩:=ih U;change likelihood R N per uk v U=_;change _=(((likelihood R N per uk v U).re:ℝ):ℂ);rw [ha];rfl
    have paid (U):0≤(Z U).re:=by obtain ⟨a,ha,eq⟩:=ih U;change 0≤(likelihood R N per uk v U).re;rw [eq];exact ha
    refine ⟨∫U,S.density β W U*(Z U).re ∂prior G _,integral_nonneg (fun U=>mul_nonneg (S.density_positive β W U) (paid U)),?_⟩
    change backTo R.family.path N per (Nat.le_succ_of_le uk) (last R u N per v) W=_
    rw [backTo_next R.family.path N per uk]
    change (∫U,(S.density β W U:ℂ)*Z U ∂prior G _)=_
    rw [←integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with U
    rw [Complex.ofReal_mul,←plotted U]

def price {u k:ℕ} (N per:ℕ) (uk:u+1≤k) (v:Config G (R.family.side u per)) (W:Config G (R.family.side k per)):ℝ:=
  (likelihood R N per uk v W).re

theorem positive {u k:ℕ} (N per:ℕ) (uk:u+1≤k) (v:Config G (R.family.side u per)) (W:Config G (R.family.side k per)):
    0≤price R N per uk v W ∧ likelihood R N per uk v W=(price R N per uk v W:ℂ) := by
  obtain ⟨a,pos,eq⟩:=retained R N per uk v W
  simp only [price,eq,Complex.ofReal_re,true_and,pos]

private theorem mass {u k N per:ℕ} (uk:u+1≤k) (live:k≤N) (v:Config G (R.family.side u per)) :
    (∫W,price R N per uk v W ∂scene R.family.path N per k)=dose (H:=R.family.path) (p:=per) u v N := by
  let μ:=scene R.family.path N per k
  let η:=scene R.family.path N per (u+1)
  let Z:=likelihood R N per uk v
  let D:=dose (H:=R.family.path) (p:=per) u v N
  letI:IsProbabilityMeasure μ:=probability (H:=R.family.path) R.makes.wilson live
  have fixed:(∫W,last R u N per v W ∂η)=(D:ℂ):=by
    change (∫W,(raw R u N per v W:ℂ) ∂η)=(D:ℂ)
    rw [integral_complex_ofReal,WilsonMacroscopicRichFlatFibre.mass R (uk.trans live) per v]
  have norm:(∫W,Z W ∂μ)=(D:ℂ):=(Therm.retro (H:=R.family.path) R.makes.wilson (p:=per) uk live _ (held R u N per v)).trans fixed
  exact (integral_re ((enrolled R N per uk v).integrableC μ)).trans (congrArg Complex.re norm)

/-- Original simultaneous posterior on all the stage k links at once. -/
def law {u k:ℕ} (N per:ℕ) (uk:u+1≤k) (v:Config G (R.family.side u per)) : Measure (Config G (R.family.side k per)):=
  (scene R.family.path N per k).withDensity (fun W=>ENNReal.ofReal (price R N per uk v W/dose (H:=R.family.path) (p:=per) u v N))

theorem prob {u k N per:ℕ} (uk:u+1≤k) (live:k≤N) (v:Config G (R.family.side u per)):
    IsProbabilityMeasure (law R N per uk v) := by
  let μ:=scene R.family.path N per k
  let D:=dose (H:=R.family.path) (p:=per) u v N
  letI:IsProbabilityMeasure μ:=probability (H:=R.family.path) R.makes.wilson live
  have dp:0<D:=dose_positive (H:=R.family.path) R.makes.wilson ((Nat.le_succ u).trans (uk.trans live)) v
  have stock:Integrable (price R N per uk v) μ:=((enrolled R N per uk v).integrableC μ).re
  refine ⟨?_⟩
  change (μ.withDensity fun W=>ENNReal.ofReal (price R N per uk v W/D)) univ=1
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,←ofReal_integral_eq_lintegral_ofReal (stock.div_const D) (ae_of_all _ fun W=>div_nonneg (positive R N per uk v W).1 dp.le)]
  rw [integral_div,show (∫W,price R N per uk v W ∂μ)=D from mass R uk live v,div_self dp.ne',ENNReal.ofReal_one]

/-- The old replicated/cofactor insertion with the genuine normalized last
Wilson kernel is a literal expectation under this probability measure. -/
theorem reading {u k N per:ℕ} (uk:u+1≤k) (live:k≤N) (v:Config G (R.family.side u per))
    (X:Config G (R.family.side k per)→ℂ) (bill:Integrable X (scene R.family.path N per k)) :
    exterior (C:=R.family) (N:=N) ((Nat.le_succ u).trans uk) X v=∫W,X W ∂law R N per uk v := by
  let D:=dose (H:=R.family.path) (p:=per) u v N
  have dp:0<D:=dose_positive (H:=R.family.path) R.makes.wilson ((Nat.le_succ u).trans (uk.trans live)) v
  have meas:Measurable fun W=>price R N per uk v W/D:=((enrolled R N per uk v).meas.re).div_const _
  rw [WilsonMacroscopicRichFlatFibre.measured R uk live X bill v,law,integral_withDensity_eq_integral_toReal_smul meas.ennreal_ofReal (Eventually.of_forall fun _=>ENNReal.ofReal_lt_top),←integral_div]
  apply integral_congr_ae
  filter_upwards [] with W
  rw [ENNReal.toReal_ofReal (div_nonneg (positive R N per uk v W).1 dp.le),Complex.real_smul,Complex.ofReal_div,(positive R N per uk v W).2]
  ring

end YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw

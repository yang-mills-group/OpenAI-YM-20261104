import YM.Integration.WilsonLocalHeldDerivatives
import YM.Integration.WilsonRegisteredPlaquetteReading
import YM.Integration.ActualScalarTransport

/-! The curvature complement used in the local action expansion has small
mass in the genuine fine Wilson marginal. A correlated spectator spends its
actual second moment. No bound on its maximum on the rejected sector enters. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalHeldCurvatureMarginal
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open WilsonReportingForestPivots WilsonReportingRegisteredAction
open scoped Classical BigOperators ENNReal Topology
variable {G:Gauge} {I:Type} [Fintype I]

theorem aperture (R:Run G) (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠm:ℕ in atTop,∀N,m<N→∀per (o:I→Site (R.family.side (m+1) per)),
    Real.sqrt ((scene R.family.path N per (m+1)).real (cold R m per d o)ᶜ)≤ε*(regulatorRun R.family N per (m+1))^q := by
  let Z:=fun i=>depth R (d i)+3
  let n:ℝ:=Fintype.card I
  let η:=ε^2/(n+1)
  have n₀:0≤n:=Nat.cast_nonneg _
  have epη:0<η:=div_pos (sq_pos_of_pos ep) (by linarith)
  filter_upwards [WilsonReportingForestBlocks.dates R.family simple slow (Finset.univ.sup Z) (ε:=1) zero_lt_one,
    (tendsto_add_atTop_nat 1).eventually (rare stoves simple R.makes.wilson),
    (tendsto_add_atTop_nat 1).eventually (WilsonRegisteredPlaquetteReading.currency R.family R.makes simple 1 (2*q) epη)] with m size buy price N live per o
  let μ:=scene R.family.path N per (m+1)
  let b:=R.family.path.levels.clock.hatBeta (m+1)
  let g:=regulatorRun R.family N per (m+1)
  let E:=fun i=> (House.chilly (G:=G) (faces R m per (d i) (o i)) (cool R.family.path.levels (m+1)))ᶜ
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live
  have cost (i:I): μ.real (E i)≤η*g^(2*q) := by
    have one:=House.cool_miss (vanishP R.family.path.levels (m+1)) (buy N live per) (faces R m per (d i) (o i))
    have cell:= (size per (Z i) (Finset.le_sup (s:=Finset.univ) (f:=Z) (Finset.mem_univ i))).2.2 (o i)
    exact one.trans ((mul_le_mul_of_nonneg_right cell (Real.exp_pos _).le).trans (by simpa only [pow_one,vanishP,g] using price N per live))
  have eq:(cold R m per d o)ᶜ=⋃i,E i:=Set.compl_iInter _
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have total:μ.real (cold R m per d o)ᶜ ≤ (ε*g^q)^2 := by
    rw [eq]
    calc
      _ ≤ ∑i,μ.real (E i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑_i:I,η*g^(2*q) := sum_le_sum fun i _=>cost i
      _ = n*(η*g^(2*q)) := by simp [n,nsmul_eq_mul]
      _ ≤ (n+1)*(η*g^(2*q)) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg epη.le (pow_nonneg gp _))
      _ = (ε*g^q)^2 := by unfold η;rw [mul_comm 2 q,pow_mul,mul_pow];field_simp
  exact (Real.sqrt_le_sqrt total).trans_eq (Real.sqrt_sq (mul_nonneg ep.le (pow_nonneg gp _)))

theorem push (R:Run G) {N per m:ℕ} (live:m<N) {F:Config G (R.family.side (m+1) per)→ℝ} (env:Envelope F) :
    let A:=actualAverage R.family (N:=N) F
    Integrable A (scene R.family.path N per m) ∧
      (∫V,A V ∂scene R.family.path N per m)=∫U,F U ∂scene R.family.path N per (m+1) := by
  intro A
  have one:actualTransport R.family (N:=N) F (Nat.le_succ m)=A:=by
    rw [actualTransport_step R.family R.makes live F (Nat.lt_succ_self m),actualTransport_base R.family R.makes live]
  let me:=env.meas.aestronglyMeasurable (μ:=prior G _)
  have hi:=actualTransport_weighted_integrable R.family R.makes live me env.cost.choose_spec le_rfl
  rw [actualTransport_base R.family R.makes live] at hi
  have low:=actualTransport_weighted_integrable R.family R.makes live me env.cost.choose_spec (Nat.le_succ m)
  exact ⟨one ▸ actualScene_integrable_of_weighted R.family R.makes live.le low,one ▸ actualScene_transport R.family R.makes live hi (Nat.le_succ m)⟩

theorem tested {X:Type*} [MeasurableSpace X] (μ:Measure X) [IsFiniteMeasure μ] {E:Set X}
    (me:MeasurableSet E) (H:X→ℝ) (env:Envelope H) :
    (∫U,E.indicator (fun x=>|H x|) U ∂μ) ≤ Real.sqrt (μ.real E)*Real.sqrt (∫U,‖H U‖^2 ∂μ) := by
  let f:=E.indicator (fun _=>(1:ℝ))
  have f₂:MemLp f (ENNReal.ofReal (2:ℝ)) μ:=(memLp_const 1).indicator me
  have h₂:MemLp H (ENNReal.ofReal (2:ℝ)) μ:=MemLp.of_bound env.meas.aestronglyMeasurable env.cost.choose (ae_of_all _ env.cost.choose_spec)
  have stock (U):‖f U‖^2=f U:=by
    by_cases hit:U∈E
    · simp only [f,indicator_of_mem hit,norm_one,one_pow]
    · simp [f,hit]
  have mixed (U):‖f U‖*‖H U‖=E.indicator (fun x=>|H x|) U:=by
    by_cases hit:U∈E
    · simp only [f,indicator_of_mem hit,norm_one,one_mul,Real.norm_eq_abs]
    · simp [f,hit]
  have cs:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two f₂ h₂
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow,mixed,stock] at cs
  simpa only [f,integral_indicator me,setIntegral_const,smul_eq_mul,mul_one] using cs

theorem absolute {X:Type*} [MeasurableSpace X] {H:X→ℝ} (env:Envelope H) {E:Set X} (me:MeasurableSet E) :
    Envelope (E.indicator (fun U=>|H U|)) := by
  refine ⟨env.meas.abs.indicator me,env.cost.choose,fun U=>(norm_indicator_le_norm_self _ _).trans ?_⟩
  simpa only [Real.norm_eq_abs,abs_abs] using env.cost.choose_spec U

theorem original (R:Run G) (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠm:ℕ in atTop,∀N,m<N→∀per (o:I→Site (R.family.side (m+1) per)) (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let upper:=scene R.family.path N per (m+1)
    let lower:=scene R.family.path N per m
    let rejected:=actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|))
    Integrable rejected lower ∧ (∫V,rejected V ∂lower)≤ε*g^q*Real.sqrt (∫U,‖H U‖^2 ∂upper) := by
  filter_upwards [aperture R stoves simple slow d q ep] with m law N live per o H env
  intro C g upper lower rejected
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  letI:IsProbabilityMeasure upper:=probability R.makes.wilson live
  obtain ⟨fund,mean⟩:=push R live (absolute env ms.compl)
  exact ⟨fund,mean.le.trans ((tested upper ms.compl H env).trans (mul_le_mul_of_nonneg_right (law N live per o) (Real.sqrt_nonneg _)))⟩

end YM.Integration.WilsonLocalHeldCurvatureMarginal

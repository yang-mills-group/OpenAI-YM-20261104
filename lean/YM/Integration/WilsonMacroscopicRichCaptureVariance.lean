import YM.Integration.WilsonMacroscopicRichFlatFibre
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCaptureVariance
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Multi Extraction Table Push.GridApprox OPE OPE.Therm
open PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}{c f:Side}

private theorem square {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : α→ℂ} (env : Envelope F) : Integrable (fun x=>‖F x‖^2) μ := by
  obtain ⟨M,bound⟩ := env.cost
  refine (integrable_const (max M 0 ^ (2:ℕ))).mono' (env.meas.norm.pow_const 2).aestronglyMeasurable ?_
  exact ae_of_all μ fun x=>by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((bound x).trans (le_max_left _ _)) 2

private theorem schwarz {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A B : α→ℂ) (ma : Measurable A) (mb : Measurable B)
    (ia : Integrable (fun x=>‖A x‖^2) μ) (ib : Integrable (fun x=>‖B x‖^2) μ) :
    ‖∫ x,A x*B x ∂μ‖ ≤ Real.sqrt (∫ x,‖A x‖^2 ∂μ)*Real.sqrt (∫ x,‖B x‖^2 ∂μ) := by
  let a := fun x=>‖A x‖
  let b := fun x=>‖B x‖
  have ha : MemLp a 2 μ := (memLp_two_iff_integrable_sq ma.norm.aestronglyMeasurable).2 ia
  have hb : MemLp b 2 μ := (memLp_two_iff_integrable_sq mb.norm.aestronglyMeasurable).2 ib
  have holder:=integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (show (0:α→ℝ) ≤ᵐ[μ] a from ae_of_all μ fun x=>norm_nonneg _)
    (show (0:α→ℝ) ≤ᵐ[μ] b from ae_of_all μ fun x=>norm_nonneg _)
    (by norm_num; exact ha) (by norm_num; exact hb)
  calc
    ‖∫ x,A x*B x ∂μ‖ ≤ ∫ x,a x*b x ∂μ := by
      simpa only [a,b,norm_mul] using (norm_integral_le_integral_norm (μ:=μ) (fun x=>A x*B x))
    _ ≤ _ := by simpa [a,b,Real.rpow_two,Real.sqrt_eq_rpow] using holder

private theorem weighted {Ω:Type*}[MeasurableSpace Ω](ν:Measure Ω)[IsFiniteMeasure ν](d:Ω→ℝ){F:Ω→ℂ}(e:Envelope F)(md:Measurable d)(dp:∀V,0≤d V)(grant:∃C:ℝ,∀V,d V≤C)(normal:(∫V,d V ∂ν)=1):‖∫V,(d V:ℂ)*F V ∂ν‖^2 ≤ ∫V,d V*‖F V‖^2 ∂ν:=by
  let A (V:Ω):ℂ:=Real.sqrt (d V)
  obtain ⟨C,B⟩:=grant
  have env:Envelope A:=by
    refine ⟨Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp md),Real.sqrt C,fun V=>?_⟩
    change ‖((Real.sqrt (d V):ℝ):ℂ)‖≤Real.sqrt C;rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)];exact Real.sqrt_le_sqrt (B V)
  have equal (V:Ω):A V*(A V*F V)=(d V:ℂ)*F V:=by
    change ((Real.sqrt (d V):ℝ):ℂ)*(((Real.sqrt (d V):ℝ):ℂ)*F V)=(d V:ℂ)*F V
    rw [←mul_assoc,←pow_two,←Complex.ofReal_pow,Real.sq_sqrt (dp V)]
  have normA (V:Ω):‖A V‖^2=d V:=by
    change ‖((Real.sqrt (d V):ℝ):ℂ)‖^2=d V
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (dp V)]
  have left:(∫V,‖A V‖^2 ∂ν)=1:=by simp_rw [normA];exact normal
  let D:=∫V,d V*‖F V‖^2 ∂ν
  have right:(∫V,‖A V*F V‖^2 ∂ν)=D:=by simp_rw [norm_mul,mul_pow,normA];rfl
  have measured:=schwarz ν A (fun V=>A V*F V) env.meas (env.mulC e).meas (square ν env) (square ν (env.mulC e))
  simp_rw [equal] at measured;rw [left,right,Real.sqrt_one,one_mul] at measured
  have pos:0≤D:=integral_nonneg (fun V=>mul_nonneg (dp V) (sq_nonneg _))
  exact (pow_le_pow_left₀ (norm_nonneg _) measured 2).trans (Real.sq_sqrt pos).le

private theorem real_energy {Ω:Type*}[MeasurableSpace Ω](ν:Measure Ω)(d:Ω→ℝ)(F:Ω→ℂ):
    (∫V,(d V:ℂ)*((‖F V‖^2:ℝ):ℂ) ∂ν).re=∫V,d V*‖F V‖^2 ∂ν:=by
  simp only [←Complex.ofReal_mul,integral_complex_ofReal,Complex.ofReal_re]

private theorem fibre {S:StepData c f}{β:ℝ}(hk:S.IsKernel β G)(U:Config G f):Measurable (S.density β U):=by
  let two:Config G c → Config G f × Config G c:=fun V=>(U,V)
  have first:Measurable (fun _V:Config G c=>U):=measurable_const
  have pair:Measurable two:=Measurable.prodMk first measurable_id
  let whole : Config G f × Config G c → ℝ:=fun a=>S.density β a.1 a.2
  have all:Measurable whole:=hk.meas
  have composed:Measurable (whole ∘ two):=all.comp pair
  exact composed

private theorem mass {S:StepData c f}{β:ℝ}(hk:S.IsKernel β G){F:Config G c→ℂ}(e:Envelope F)(U:Config G f):
    ‖back S β F U‖^2≤(back S β (fun V=>((‖F V‖^2:ℝ):ℂ)) U).re:=by
  obtain ⟨C,B⟩:=hk.bound
  have credit:=weighted (Ω:=Config G c) (prior G c) (S.density β U) (F:=F) e (fibre hk U) (hk.positive U) ⟨C,B U⟩ (hk.total U)
  exact credit.trans (real_energy (prior G c) (S.density β U) F).symm.le

private theorem power {Ω:Type*}[MeasurableSpace Ω]{Z:Ω→ℂ}(e:Envelope Z):Envelope (fun U=>((‖Z U‖^2:ℝ):ℂ)):=by
  refine ⟨Complex.continuous_ofReal.measurable.comp (e.meas.norm.pow_const 2),?_⟩
  obtain ⟨C,B⟩:=e.cost;refine ⟨C^2,fun U=>?_⟩
  rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)];exact pow_le_pow_left₀ (norm_nonneg _) (B U) 2

/-- The original derived energy inequality for any genuine coarser capture field (including a fully correlated signed exterior, with no factorization). Every stage uses the same true Wilson measures of the same N and period. -/
theorem measured (R:Run G){N p b k:ℕ}(bk:b≤k)(kN:k≤N){Z:Config G (R.family.side b p)→ℂ}(e:Envelope Z):
    (∫U,‖backTo R.family.path N p bk Z U‖^2 ∂scene R.family.path N p k)≤∫U,‖Z U‖^2 ∂scene R.family.path N p b:=by
  let H:=R.family.path
  induction k,bk using Nat.le_induction with
  | base=>simp
  | succ k bk ih =>
    have old:=bk.trans (Nat.le_succ k);have q:=Nat.le_succ k;let X:=backTo H N p bk Z
    let T:=H.levels.clock.op k p;let β:=H.β N p (k+1);let V:=fun U:Config G (R.family.side k p)=>((‖X U‖^2:ℝ):ℂ)
    have xe:Envelope X:=backTo_env H N p bk e;have ve:Envelope V:=power xe
    let μ:=scene H N p (k+1);letI:IsProbabilityMeasure μ:=probability R.makes.wilson kN
    let lowerlaw:=scene H N p k;letI:IsProbabilityMeasure lowerlaw:=probability R.makes.wilson (q.trans kN)
    have out:Envelope (back T β X):=back_env (H.levels.transition_mass ..) xe
    have obs:Envelope (back T β V):=back_env (H.levels.transition_mass ..) ve
    have proj:(∫U,back T β V U ∂μ)=∫U,V U ∂lowerlaw:=by
      have exactRead:=Therm.retro R.makes.wilson (p:=p) q kN V ve
      change (∫U,backTo H N p q V U ∂μ)=∫U,V U ∂lowerlaw at exactRead
      have agree:backTo H N p q V=back T β V:=by rw [backTo_next H N p (le_rfl:k≤k) V,backTo_self]
      rw [agree] at exactRead;exact exactRead
    have report:(∫U,(back T β V U).re ∂μ)=∫U,‖X U‖^2 ∂lowerlaw:=by
      have left:=integral_re (obs.integrableC μ);have right:=integral_re (ve.integrableC lowerlaw)
      calc _=(∫U,back T β V U ∂μ).re:=left
           _=(∫U,V U ∂lowerlaw).re:=congrArg Complex.re proj
           _=_:=right.symm
    rw [backTo_next H N p bk Z]
    calc
      _≤∫U,(back T β V U).re ∂μ:=integral_mono (square μ out) (obs.integrableC μ).re (fun U=>mass (H.levels.transition_mass ..) xe U)
      _=(∫U,‖X U‖^2 ∂lowerlaw):=report
      _≤_:=ih (q.trans kN)

end YM.Integration.WilsonMacroscopicRichCaptureVariance


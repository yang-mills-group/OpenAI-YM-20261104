import YM.Integration.WilsonMacroscopicRichFlatKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFlatFibre
open Filter Set Finset Function MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox OPE OPE.Therm Pressure
open PhysicalNext.Repeat.Legato WilsonMacroscopicRichFlatKernel
open scoped Topology BigOperators
variable {G:Gauge}

def raw (R:Run G)(u N per:ℕ)(V:Config G (R.family.side u per))(W:Config G (R.family.side (u+1) per)):ℝ:=
  (R.family.path.levels.clock.op u per).density (R.family.path.β N per (u+1)) W V

def last (R:Run G)(u N per:ℕ)(V:Config G (R.family.side u per))(W:Config G (R.family.side (u+1) per)):ℂ:=raw R u N per V W

private theorem kernel_envelope {c f:Side}(S:StepData c f)(β:ℝ)(hk:S.IsKernel β G)(V:Config G c):Envelope (fun W:Config G f=>(S.density β W V:ℂ)):=by
  let entry:Config G f × Config G c → ℂ:=fun a=>(S.density β a.1 a.2:ℂ)
  have field:Envelope entry:=(den_env hk).ofReal_env
  let g : Config G f → (Config G f × Config G c) := fun W=>(W,V)
  have map:Measurable g:=Measurable.prodMk measurable_id measurable_const
  have slab:Envelope (entry ∘ g):=field.comp_env map
  exact slab

theorem held (R:Run G)(u N per:ℕ)(V:Config G (R.family.side u per)):Envelope (last R u N per V):=
  kernel_envelope (R.family.path.levels.clock.op u per) _ (R.family.path.levels.transition_mass ..) V

/-- The normalization at the specified (possibly flat) external field is exactly the full true fine Gibbs mean, with its original Wilson partition function. -/
theorem mass (R:Run G){u N:ℕ}(live:u+1≤N)(per:ℕ)(V:Config G (R.family.side u per)):
    (∫ W,raw R u N per V W ∂scene R.family.path N per (u+1))=dose (H:=R.family.path) (p:=per) u V N:=by
  let H:=R.family.path
  let D:=partition G (H.S.side N per) (H.β N per N)
  let S:=H.levels.clock.op u per
  let β:=H.β N per (u+1)
  have step:=congrFun (R.makes.wilson.steps N per u (show u<N by omega)).1 V
  have old: (∫ W,raw R u N per V W ∂scene H N per (u+1))=(∫ W,((H.rep N per (u+1)).eval W/D) • (S.density β W V) ∂prior G (R.family.side (u+1) per)):=account (H:=H) (p:=per) R.makes.wilson live (raw R u N per V)
  apply old.trans
  refine Eq.trans ?_ (congrArg (fun z:ℝ=>z/D) step).symm
  change (∫ W,((H.rep N per (u+1)).eval W/D) • (S.density β W V) ∂prior G (R.family.side (u+1) per))=(∫ W,S.density β W V • (H.rep N per (u+1)).eval W ∂prior G (R.family.side (u+1) per))/D
  rw [←integral_div];simp only [smul_eq_mul]
  apply integral_congr_ae;filter_upwards [] with W;ring

private theorem reserve (R:Run G){u N:ℕ}(live:u+1≤N)(per:ℕ)(V:Config G (R.family.side u per)):
    let D:=dose (H:=R.family.path) (p:=per) u V N
    0<D ∧ front R u N per≤D*Real.exp (rate R u*(edges R u per:ℝ)):=by
  let μ:=scene R.family.path N per (u+1)
  let J:=front R u N per
  let a:=rate R u*(edges R u per:ℝ)
  let d:=raw R u N per V
  let D:=dose (H:=R.family.path) (p:=per) u V N
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live
  have disp:=WilsonMacroscopicRichFlatKernel.purchased R u per N live
  have intd:Integrable d μ:=((held R u N per V).integrableC μ).re
  have low:J*Real.exp (-a)≤D:=calc
    _=∫ _W:Config G (R.family.side (u+1) per),J*Real.exp (-a) ∂μ:=by
      rw [integral_const,probReal_univ,one_smul]
    _≤∫ W,d W ∂μ:=integral_mono (integrable_const _) intd (fun W=>(disp.2 W V).1)
    _=D:=mass R live per V
  refine ⟨dose_positive R.makes.wilson ((Nat.le_succ u).trans live) V,?_⟩
  calc J=J*Real.exp (-a)*Real.exp a:=by rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
       _≤D*Real.exp a:=mul_le_mul_of_nonneg_right low (Real.exp_pos _).le

private theorem disk {z:ℂ}{J:ℝ}(h:‖z+((-(J/2):ℝ):ℂ)‖≤J/2):‖z‖^2≤J*z.re:=by
  have h2:=pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Complex.sq_norm,Complex.normSq_apply] at h2 ⊢
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,add_zero] at h2
  nlinarith only [h2]

/-- Pointwise bound for the entire genuine likelihood used when a separate
    microscopic exterior is quoted by its actual Wilson second moment. -/
theorem bounded (R : Run G) {u k N : ℕ} (uk : u + 1 ≤ k) (kN : k ≤ N) (per : ℕ)
    (V : Config G (R.family.side u per)) :
    let D := dose (H := R.family.path) (p := per) u V N
    0 < D ∧ ∀ W, ‖backTo R.family.path N per uk (last R u N per V) W‖ ≤
      D * Real.exp (rate R u * (edges R u per : ℝ)) := by
  have live := uk.trans kN
  obtain ⟨dp, reserve_price⟩ := reserve R live per V
  have initial := WilsonMacroscopicRichFlatKernel.purchased R u per N live
  have cap (W) : ‖last R u N per V W‖ ≤ front R u N per := by
    have priced := initial.2 W V
    have nonnegative : 0 ≤ raw R u N per V W :=
      (mul_pos initial.1 (Real.exp_pos _)).le.trans priced.1
    change ‖((raw R u N per V W : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg nonnegative]
    exact priced.2
  have actual := backTo_bound R.family.path N per uk (held R u N per V).meas (front R u N per) cap
  exact ⟨dp, fun W => (actual W).trans reserve_price⟩

/-- The genuine scalar blocking likelihood at any finer scale stays in the disk centered at half the same Wilson prefactor. Its exact first moment gives a uniform second-moment price at each held field. -/
theorem propagated (R:Run G){u k N:ℕ}(uk:u+1≤k)(kN:k≤N)(per:ℕ)(V:Config G (R.family.side u per)):
    let D:=dose (H:=R.family.path) (p:=per) u V N
    0<D ∧ Real.sqrt (∫ W,‖backTo R.family.path N per uk (last R u N per V) W‖^2 ∂scene R.family.path N per k)≤D*Real.exp (rate R u*(edges R u per:ℝ)/2):=by
  let H:=R.family.path
  let μ:=scene H N per k
  let η:=scene H N per (u+1)
  let J:=front R u N per
  let a:=rate R u*(edges R u per:ℝ)
  let D:=dose (H:=H) (p:=per) u V N
  let F:=last R u N per V
  let Z:=backTo H N per uk F
  let c:Config G (R.family.side (u+1) per)→ℂ:=fun _=>((-(J/2):ℝ):ℂ)
  have live:=uk.trans kN
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson kN
  letI:IsProbabilityMeasure η:=probability R.makes.wilson live
  have fe:Envelope F:=held R u N per V
  have ze:Envelope Z:=backTo_env H N per uk fe
  have ce:Envelope c:=Envelope.constC _
  have disp:=WilsonMacroscopicRichFlatKernel.purchased R u per N live
  have own (W):‖(F+c) W‖≤J/2:=by
    have best:=disp.2 W V
    have low:0≤raw R u N per V W:=(mul_pos disp.1 (Real.exp_pos _)).le.trans best.1
    have high:raw R u N per V W≤J:=best.2
    change ‖((raw R u N per V W:ℝ):ℂ)+((-(J/2):ℝ):ℂ)‖≤J/2
    rw [←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [low],by linarith only [high]⟩
  have carried:=backTo_bound H N per uk (fe.meas.add ce.meas) (J/2) own
  have shift (W):backTo H N per uk (F+c) W=Z W+((-(J/2):ℝ):ℂ):=by
    rw [backTo_add H N per uk fe ce]
    change Z W+backTo H N per uk (fun _=>((-(J/2):ℝ):ℂ)) W=_
    rw [backTo_const]
  have pointwise (W):‖Z W‖^2≤J*(Z W).re:=by
    have bound:=carried W
    change ‖backTo H N per uk (F+c) W‖≤J/2 at bound
    rw [shift W] at bound
    exact disk bound
  have fixed:(∫ W,F W ∂η)=(D:ℂ):=by
    change (∫ W,(raw R u N per V W:ℂ) ∂η)=(D:ℂ)
    rw [integral_complex_ofReal,mass R live per V]
  have total:(∫ W,Z W ∂μ)=(D:ℂ):=(Therm.retro R.makes.wilson (p:=per) uk kN F fe).trans fixed
  have mean:(∫ W,(Z W).re ∂μ)=D:=(integral_re (ze.integrableC μ)).trans (congrArg Complex.re total)
  obtain ⟨C,cap⟩:=ze.cost
  have normZ:Envelope (fun W=>‖Z W‖):=⟨ze.meas.norm,C,fun W=>by
    rw [Real.norm_of_nonneg (norm_nonneg _)];exact cap W⟩
  have square:Integrable (fun W=>‖Z W‖^2) μ:=by
    simpa only [pow_two] using (normZ.mul normZ).integrable μ
  have price:(∫ W,‖Z W‖^2 ∂μ)≤J*D:=calc
    _≤∫ W,J*(Z W).re ∂μ:=integral_mono square ((ze.integrableC μ).re.const_mul J) pointwise
    _=J*D:=by rw [integral_const_mul,mean]
  obtain ⟨dp,frontPrice⟩:=reserve R live per V
  refine ⟨dp,Real.sqrt_le_iff.mpr ⟨mul_nonneg dp.le (Real.exp_pos _).le,price.trans ?_⟩⟩
  have split:(Real.exp (a/2))^2=Real.exp a:=by rw [pow_two,←Real.exp_add];congr 1;ring
  change J*D≤(D*Real.exp (a/2))^2
  rw [mul_pow,split]
  calc J*D≤(D*Real.exp a)*D:=mul_le_mul_of_nonneg_right frontPrice dp.le
       _=D^2*Real.exp a:=by ring

theorem last_moment (R:Run G){u N:ℕ}(live:u+1≤N)(per:ℕ)(V:Config G (R.family.side u per)):
    let D:=dose (H:=R.family.path) (p:=per) u V N
    0<D ∧ Real.sqrt (∫ W,‖last R u N per V W‖^2 ∂scene R.family.path N per (u+1))≤D*Real.exp (rate R u*(edges R u per:ℝ)/2):=by
  simpa only [backTo_self] using propagated R (le_rfl:u+1≤u+1) live per V

end YM.Integration.WilsonMacroscopicRichFlatFibre

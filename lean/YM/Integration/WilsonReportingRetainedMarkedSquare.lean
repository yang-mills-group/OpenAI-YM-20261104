import YM.Integration.WilsonReportingRetainedMarkedPortfolio

/-! The original rejected marked cluster with its correlated exterior
charged in the true second moment on the failed set alone. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingRetainedMarkedSquare
open Filter Function Set Finset MeasureTheory Lattice Wilson Merge RG Tree Pressure ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Lotus Daisy RGLocalTaylor MergeProof Marker Extra.Multi
open LocalLTE Matter OPE.Therm RG16 FullQLocal WilsonPositionSeparatedProfileReportingPrimary
open ManuscriptQLocalIntegratedTicket WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open WilsonReportingRetainedMarkedDiagram ManuscriptQLocalMarkedHeightTail
open WilsonReportingRetainedMarkedPortfolio
open private length_paid from YM.Integration.WilsonReportingRetainedMarkedPortfolio
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {Y:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ α:ℝ} {o:Target.Order G W}
    (H:Cash W s μ L Q o α T Y) (χ:Chi)
    {V ι:Type} [DecidableEq V] [Fintype ι] {Γ:Marker.Census V} (M:ι → Menu.Hat Γ Y)
    {j n:ℕ} {C' d v B' A b r B q:ℝ} (K:Captain H j C' d v B' A b r B q n χ)


include K in
omit [Fintype ι] in
private theorem one (τ:ℝ) (ℓ:ℕ) (z:Fan.Stars H (fun i=>(M i).M)) (low:¬Height.tiredN H ℓ z.1)
    (ν:Measure (Config G c)) [IsFiniteMeasure ν] (F:Config G c→ℂ) (C wage rate:ℝ)
    (wa:0≤wage) (r0:0≤rate) (quote:∀U,|activity H χ M z.1 z.2 U|≤wage)
    : let X:=Captain.reachability z.1
      let D:=House.chilly (G:=G) (cover X) τ
      (∀Y⊆X,∀U∈D,Healthy (Pressure.temp s) Y U) →
      ν.real Dᶜ≤(coverNumber (radiusB s) X:ℝ)*rate^2 → MemLp (Dᶜ.indicator F) 2 ν →
      Real.sqrt (∫U,‖Dᶜ.indicator F U‖^2 ∂ν)≤C →
    ‖∫U,F U*(discrepancy H χ M τ z U:ℂ) ∂ν‖ ≤ (C*wage)*((coverNumber (radiusB s) X:ℝ)*rate) := by
  classical
  intro X D clear event F2 stock
  let cnt:ℝ:=coverNumber (radiusB s) X
  have c0:0≤cnt:=Nat.cast_nonneg _
  have k2:cnt≤cnt^2:=by
    rcases Nat.eq_zero_or_pos (coverNumber (radiusB s) X) with zero|pos
    · simp [cnt,zero]
    · have h:1≤cnt:=by
        change (1:ℝ) ≤ (coverNumber (radiusB s) X:ℝ)
        exact_mod_cast (show 1≤coverNumber (radiusB s) X from pos)
      nlinarith [sq_nonneg (cnt-1)]
  have measure:Real.sqrt (ν.real Dᶜ)≤cnt*rate:=by
    rw [←Real.sqrt_sq (mul_nonneg c0 r0)]
    apply Real.sqrt_le_sqrt
    rw [mul_pow]
    exact event.trans (mul_le_mul_of_nonneg_right k2 (sq_nonneg rate))
  let b:=Dᶜ.indicator (fun _=>(1:ℝ))
  let f:=Dᶜ.indicator F
  have closed:MeasurableSet Dᶜ:=(House.bath _).compl
  have b2:MemLp b 2 ν:=(memLp_const 1).indicator closed
  have f2:MemLp f 2 ν:=F2
  have exponent:ENNReal.ofReal (2:ℝ)=2:=by norm_num
  have bh:MemLp b (ENNReal.ofReal (2:ℝ)) ν:=exponent.symm ▸ b2
  have fh:MemLp (fun U=>‖f U‖) (ENNReal.ofReal (2:ℝ)) ν:=exponent.symm ▸ f2.norm
  have cs:=integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two bh fh
  have id (U):‖b U‖^2=b U:=by
    by_cases failed:U∈Dᶜ <;> simp [b,failed]
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow,norm_norm,id] at cs
  change (∫U,‖b U‖*‖f U‖ ∂ν) ≤ Real.sqrt (∫ U,b U ∂ν)*Real.sqrt (∫U,‖f U‖^2 ∂ν) at cs
  have total:(∫U,b U ∂ν)=ν.real Dᶜ:=by simp only [b,integral_indicator closed,setIntegral_const,smul_eq_mul,mul_one]
  rw [total] at cs
  have maj:Integrable (fun U=>‖b U‖*‖f U‖) ν:=b2.norm.integrable_mul f2.norm
  calc
    _≤∫U,‖F U*(discrepancy H χ M τ z U:ℂ)‖ ∂ν:=norm_integral_le_integral_norm _
    _≤∫U,wage*(‖b U‖*‖f U‖) ∂ν:=by
      apply integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) (maj.const_mul wage)
      apply ae_of_all
      intro U
      change ‖F U*((activity H χ M z.1 z.2 U-D.indicator (field H χ M z.1 z.2) U:ℝ):ℂ)‖≤_
      by_cases fit:U∈D
      · rw [Set.indicator_of_mem fit,accepted H χ M K ℓ z.1 low z.2 U (fun Y hY=>clear Y hY U fit),
          sub_self,Complex.ofReal_zero,mul_zero,norm_zero]
        exact mul_nonneg wa (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · have failed:U∈Dᶜ:=fit
        simp only [Set.indicator_of_notMem fit,sub_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,b,f,
          Set.indicator_of_mem failed,norm_one,one_mul]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (quote U) (norm_nonneg (F U))
    _=wage*(∫U,‖b U‖*‖f U‖ ∂ν):=integral_const_mul _ _
    _≤wage*((cnt*rate)*C):=mul_le_mul_of_nonneg_left (cs.trans (mul_le_mul measure stock (Real.sqrt_nonneg _) (mul_nonneg c0 r0))) wa
    _=_:=by ring

private theorem funded [Fintype V] (host:HostQ H K.conduit A B n) (Z:BudgetPoint) (th:Z.threshold=Pressure.temp s)
    (ord:Z.order ≤ j) (a:ℕ) (power:Z.power ≤ a) (ℓ:ℕ) (w:V → ℝ) (hw:∀v,0<w v) (hβ:1 ≤ betaF G s L)
    (γ:ℝ) (u:ℝ) (before:Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*Height.markU K (fun i=>(M i).M)
        (fun i=>(betaF G s L)^(-(2:ℝ))*Menu.sumFee (M i) w) z a) (γ+1) u)
    (ν:Measure (Config G c)) (finite:IsFiniteMeasure ν) (τ rate:ℝ) (l0:0 ≤ rate)
    (event:∀X:Support c,ν.real (House.chilly (G:=G) (cover X) τ)ᶜ ≤ (coverNumber (radiusB s) X:ℝ)*rate^2 ∧
      ∀Y⊆X,∀U∈House.chilly (G:=G) (cover X) τ,Healthy (Pressure.temp s) Y U)
    (F:Fan.Stars H (fun i=>(M i).M) → Config G c → ℂ) (C:ℝ) (C0:0 ≤ C)
    (rough:∀z,¬Height.tiredN H ℓ z.1 →
      let D:=House.chilly (G:=G) (cover (Captain.reachability z.1)) τ
      MemLp (Dᶜ.indicator (F z)) 2 ν ∧ Real.sqrt (∫U,‖Dᶜ.indicator (F z) U‖^2 ∂ν)≤C) :
    Ac.Hit (fun z:Fan.Stars H (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB s)
      (fun z=>if ¬Height.tiredN H ℓ z.1 then Poly.price w (WilsonReportingRetainedMarkedPortfolio.signed H χ M τ ν F z) else 0)
      γ ((C*rate)*((((betaF G s L)^2)^Fintype.card V)*u)) := by
  letI:=finite
  have sale:=ManuscriptQLocalSmoothSourceTail.funded H M K a ℓ w hw hβ before
  have raw (z:Fan.Stars H (fun i=>(M i).M)):0 ≤ Captain.wife K z.1 (fun i=>(M i).M) z.2 a:=
    mul_nonneg (pow_nonneg (by unfold March.shiftG;positivity) _) (Captain.fareV K z.1 _ z.2)
  intro root
  apply budget_mono (budget_scale (mul_nonneg C0 l0) (sale root))
  · intro z
    by_cases seen:root∈Captain.reachability z.1
    · simp only [if_pos seen]
      apply mul_nonneg _ (Real.exp_pos _).le
      split_ifs <;> first | exact le_rfl | exact Poly.nonnegative hw _
    · simp only [if_neg seen,le_refl]
  · intro z
    by_cases seen:root∈Captain.reachability z.1
    · simp only [if_pos seen]
      by_cases low:¬Height.tiredN H ℓ z.1
      · simp only [if_pos low,WilsonReportingRetainedMarkedPortfolio.signed,Poly.adapted]
        let X:=Captain.reachability z.1
        let k:ℝ:=coverNumber (radiusB s) X
        let amount:=Captain.wife K z.1 (fun i=>(M i).M) z.2 a
        let mass:=Poly.price w (matrix H M z)
        let zread:=fun U=>F z U*(discrepancy H χ M τ z U:ℂ)
        have m0:0 ≤ mass:=Poly.nonnegative hw _
        have a0:0 ≤ amount:=raw z
        have quote (U):|activity H χ M z.1 z.2 U| ≤ amount:=by
          apply (ManuscriptQLocalObservedComponents.value H χ M K host Z th ord a power z root seen U).trans
          split_ifs <;> first | exact le_rfl | exact a0
        have val:‖∫U,zread U ∂ν‖ ≤ (C*amount)*(k*rate):=one H χ M K τ ℓ z low ν (F z) C amount rate a0 l0 quote
          (event X).2 (event X).1 (rough z low).1 (rough z low).2
        change ‖∫U,zread U ∂ν‖*mass*Real.exp (γ*k) ≤ (C*rate)*((mass*amount)*Real.exp ((γ+1)*k))
        calc
          _ ≤ ((C*amount)*(k*rate))*mass*Real.exp (γ*k):=by gcongr
          _=((C*rate)*(mass*amount))*(k*Real.exp (γ*k)):=by ring
          _ ≤ ((C*rate)*(mass*amount))*Real.exp ((γ+1)*k):=mul_le_mul_of_nonneg_left (length_paid γ k) (by positivity)
          _=_:=by ring
      · simp only [if_neg low,zero_mul]
        exact mul_nonneg (mul_nonneg C0 l0) (mul_nonneg (mul_nonneg (Poly.nonnegative hw _) (raw z)) (Real.exp_pos _).le)
    · simp only [if_neg seen,mul_zero,le_refl]

/-- The genuine RMS need only hold on each original failed support. -/
theorem original {V:Type} [Fintype V] [DecidableEq V] (Γ:Marker.Census V) (req:FullQLocal.RenderedStep.Request V)
    (R:Run G) (simple:G.Simple) (gate:posted R) (p:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N,(m+1)<N → ∀per,
    let β:=R.family.path.levels.clock.hatBeta (m+1)
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    let ν:=scene R.family.path N per (m+1)
    ∀{P:Teller G} {Q:ConnectedActivityE6.Target G P} {W μ α:ℝ} {L:Side} {O:Target.Order G W}
    {Y:Rep G (R.family.side (m+2) per)} (J:Cash W β μ L Q O α (Testing.ships R.alloy.B N (m+1) per) Y)
    (E:Q.Expense) {high:ℝ},ManuscriptQLocalMarkedHeightRun.High E J req Γ high → 
    ∀(ι:Type) [Fintype ι] (M:ι → Menu.Hat Γ Y) (origin:V → Site (R.family.side (m+2) per)) (w:V → ℝ) (offer:ℝ),
    (∀v,0<w v) → Menu.Offer origin M w Y.p.B Y.p.supportExponent offer → (Fintype.card V:ℝ)*offer ≤ betaF G β L → 
    let ℓ:=ManuscriptQLocalMarkedHeightRun.length req
    ∀(F:Fan.Stars J (fun i=>(M i).M) → Config G (R.family.side (m+1) per) → ℂ) {C:ℝ},0 ≤ C → 
    (∀z,¬Height.tiredN J ℓ z.1 →
      let D:=House.chilly (G:=G) (cover (Captain.reachability z.1)) (angularCut β)
      MemLp (Dᶜ.indicator (F z)) 2 ν ∧ Real.sqrt (∫U,‖Dᶜ.indicator (F z) U‖^2 ∂ν)≤C) → 
    Ac.Hit (fun z:Fan.Stars J (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB β)
      (fun z=>if ¬Height.tiredN J ℓ z.1 then Poly.price w (WilsonReportingRetainedMarkedPortfolio.signed J Chi.canonical M (angularCut β) ν F z) else 0)
      (E.earn-1) ((C*(ε*g^p))*(((betaF G β L)^2)^Fintype.card V)) := by
  filter_upwards [WilsonReportingMolecularMaskRegion.purchased R simple gate (2*p) (sq_pos_of_pos ep)] with
    m solar N live per β g ν P Q W μ α L O Y J E high housed ι _ M origin w offer hw saved cap ℓ F C C0 rough
  obtain ⟨A,b,C',d,v,s,r,B,e,q,k,K,_,host,_,window,market⟩:=housed
  let Z:BudgetPoint:={ R.family.path.levels.budget (m+1) with
    order:=req.outputFieldOrder,order_ge:=req.field_minimum,power:=req.outputDistanceOrder,power_ge:=req.distance_minimum }
  letI:IsProbabilityMeasure ν:=probability R.makes.wilson (by omega:m+1 ≤ N)
  have l0:0 ≤ ε*g^p:=by dsimp [g,Pert.Asymptotics.regulatorRun];positivity
  have fee:=((market ι M origin w offer hw saved cap).1)
  have bought:=funded J Chi.canonical M K host Z rfl le_rfl req.outputDistanceOrder le_rfl ℓ w hw
    window.1 (E.earn-1) 1 (by simpa only [sub_add_cancel] using fee)
    ν (inferInstance:IsFiniteMeasure ν) (angularCut β) (ε*g^p) l0 (fun X => ⟨by rw [mul_pow,←pow_mul,Nat.mul_comm p 2];exact (solar N (by omega) per X).1,
      (solar N (by omega) per X).2⟩) F C C0 rough
  simpa only [mul_one] using bought

end YM.Integration.WilsonReportingRetainedMarkedSquare

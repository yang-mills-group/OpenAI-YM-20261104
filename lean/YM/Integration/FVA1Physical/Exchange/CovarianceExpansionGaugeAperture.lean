import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionGaugeWindowIntegral

/-! The original probability mass of a pure-gauge patch cancels before
estimating the three-point measurement. Only the actual physical event
and the reference density *inside* that same gauge patch occur. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function MeasureTheory Filter Set Lattice RG Wilson
open scoped Classical BigOperators
open private proper_product_env from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionForestSevenAction
variable {G:Gauge}{f:Side}

private theorem real_patch_integral (e:Lattice.Edge (Site f))(distinct:e.1+step e.2≠e.1)
    (A:Set G.El)(ma:MeasurableSet A)(u:Config G f→ℝ)(eu:Envelope u)
    (sym:∀g U,u (gauge (endpointGauge e.1 g) U)=u U):
    (∫U in openPatch e A,u U ∂prior G f)=G.probHaar.real A*(∫U,u U ∂prior G f):=by
  have s:=true_patch_integral e distinct A ma (fun x=>(u x:ℂ)) eu.ofReal_env
    (fun g U=>congrArg Complex.ofReal (sym g U))
  apply Complex.ofReal_injective
  have R(ν:Measure (Config G f)):(∫x,(u x:ℂ) ∂ν)=Complex.ofReal (∫x,u x ∂ν):=integral_ofReal (𝕜:=ℂ) (μ:=ν) (f:=u)
  simpa only [R,Complex.real_smul,Complex.ofReal_mul] using s

private theorem real_patch_event (e:Lattice.Edge (Site f))(distinct:e.1+step e.2≠e.1)
    (A:Set G.El)(ma:MeasurableSet A)(B:Set (Config G f))(mb:MeasurableSet B)
    (symB:∀g U,gauge (endpointGauge e.1 g) U∈B ↔ U∈B)
    (u:Config G f→ℝ)(eu:Envelope u)(sym:∀g U,u (gauge (endpointGauge e.1 g) U)=u U):
    (∫U in B,u U ∂(prior G f).restrict (openPatch e A))=
    G.probHaar.real A*(∫U in B,u U ∂prior G f):=by
  obtain ⟨M,hm⟩:=eu.cost
  have eg:Envelope (B.indicator u):=⟨eu.meas.indicator mb,max M 0,fun x=>by
    by_cases h:x∈B
    · rw [Set.indicator_of_mem h];exact (hm x).trans (le_max_left ..)
    · rw [Set.indicator_of_notMem h,norm_zero];exact le_max_right ..⟩
  have inv(g U):(B.indicator u) (gauge (endpointGauge e.1 g) U)=(B.indicator u) U:=by
    by_cases h:U∈B
    · rw [indicator_of_mem h,indicator_of_mem ((symB g U).mpr h),sym]
    · rw [indicator_of_notMem h,indicator_of_notMem (fun k=>h ((symB g U).mp k))]
  have cut:=real_patch_integral e distinct A ma (B.indicator u) eg inv
  simpa only [integral_indicator mb] using cut

theorem open_patch_common_read (e:Lattice.Edge (Site f))(distinct:e.1+step e.2≠e.1)
    (A:Set G.El)(ma:MeasurableSet A)(positive:0<G.probHaar.real A)
    (u:Config G f→ℝ)(eu:Envelope u)(stable:∀g U,u (gauge (endpointGauge e.1 g) U)=u U)
    (F:Config G f→ℂ)(ef:Envelope F)(phys:∀g U,F (gauge (endpointGauge e.1 g) U)=F U):
    FrozenRead.meanOn ((prior G f).restrict (openPatch e A)) u F=FrozenRead.meanOn (prior G f) u F:=by
  let γ:=G.probHaar.real A
  have denominator:=real_patch_integral e distinct A ma u eu stable
  have z:Envelope (fun U=>u U • F U):=by
    simpa only [Complex.real_smul] using Multi.Leaf.multiply eu.ofReal_env ef
  have num:=true_patch_integral e distinct A ma (fun U=>u U • F U) z
    (fun g U=>congrArg₂ (· • ·) (stable g U) (phys g U))
  unfold FrozenRead.meanOn
  rw [denominator,num,mul_inv,smul_smul]
  rw [mul_comm (G.probHaar.real A)⁻¹ (∫x,u x ∂prior G f)⁻¹,mul_assoc,inv_mul_cancel₀ positive.ne',mul_one]

/-- The full physical triple is compared to a separately normalized reference
on P∩B, where P fixes one free Haar bond to a positive patch. No invariance is
required of the reference. Haar(P) disappears entirely. -/
theorem physical_gauge_patch_rate (e:Lattice.Edge (Site f))(distinct:e.1+step e.2≠e.1)
    (A:Set G.El)(ma:MeasurableSet A)(γp:0<G.probHaar.real A)
    (B:Set (Config G f))(bm:MeasurableSet B)(symB:∀g U,gauge (endpointGauge e.1 g) U∈B ↔ U∈B)
    {k a b r:Config G f→ℝ}(km:Measurable k)(am:Measurable a)(bb:Measurable b)(kn:∀x,0≤k x)
    (ap:∀x,0<a x)(bp:∀x,0<b x)(rm:Measurable r)(anchor:ℝ)
    (same:∀x,Real.log (a x)-Real.log (b x)=r x+anchor)
    (t:ℝ)(tn:0≤t)(h:Fin 3 → Config G f→ℂ)(eh:∀i,Envelope (h i))
    (phys:∀i g U,h i (gauge (endpointGauge e.1 g) U)=h i U)
    (L:Fin 3→ℝ)(ln:∀i,0≤L i)(pay:∀i x,‖h i x‖≤L i):
    let u:=fun x=>k x*a x;let v:=fun x=>k x*b x;let μ:=prior G f
    let M:=openPatch e A∩B;let ν:=μ.restrict M
    let U:=fun s=>FrozenRead.meanOn μ u (physicalProperRows h s)
    let V:=fun s=>FrozenRead.meanOn ν v (physicalProperRows h s)
    let z:=∫x,u x ∂μ;let c:=∫x in B,u x ∂μ;let q:=∫x,v x ∂ν
    Envelope u → (∀g x,u (gauge (endpointGauge e.1 g) x)=u x) →
    Integrable v ν → 0<z → 0<c → 0<q →
    (∀x∈M,∀y∈M,Replica.cap (r x-r y)≤t) →
    z*‖properThree U-properThree V‖≤26*L 0*L 1*L 2*(c*t+∫x in Bᶜ,u x ∂μ):=by
  intro u v μ M ν U V z c q eu stable vi zp cp qp fee
  let γ:=G.probHaar.real A
  let P:=openPatch e A
  let ρ:=μ.restrict P
  have pm:MeasurableSet P:=(measurable_pi_apply e) ma
  have mm:MeasurableSet M:=pm.inter bm
  have pin:ρ.restrict M=ν:=by
    change (μ.restrict P).restrict (P∩B)=μ.restrict (P∩B)
    rw [Measure.restrict_restrict (pm.inter bm)]
    congr 1;ext x;simp [and_left_comm,and_comm]
  have entry:ρ.restrict M=ρ.restrict B:=by
    change (μ.restrict P).restrict (P∩B)=(μ.restrict P).restrict B
    rw [pin,Measure.restrict_restrict bm]
    exact congrArg μ.restrict (inter_comm P B)
  have wg:(∫x,u x ∂ρ)=γ*z:=real_patch_integral e distinct A ma u eu stable
  have wc:(∫x in M,u x ∂ρ)=γ*c:=by rw [entry];exact real_patch_event e distinct A ma B bm symB u eu stable
  have wh:(∫x in Mᶜ,u x ∂ρ)=γ*(∫x in Bᶜ,u x ∂μ):=by
    have d₁:=integral_add_compl mm (eu.integrable ρ)
    have d₂:=integral_add_compl bm (eu.integrable μ)
    rw [wc,wg] at d₁
    change c+(∫x in Bᶜ,u x ∂μ)=z at d₂
    linear_combination d₁-γ*d₂
  have wp:0<(∫x,u x ∂ρ):=wg.trans_gt (mul_pos γp zp)
  have cc:0<(∫x in M,u x ∂ρ):=wc.trans_gt (mul_pos γp cp)
  have vp:0<(∫x in M,v x ∂ρ):=by rw [pin];exact qp
  have vi':Integrable v (ρ.restrict M):=pin.symm ▸ vi
  have env:=proper_product_env h eh
  have sym(s:Fin 7)(g U):physicalProperRows h s (gauge (endpointGauge e.1 g) U)=physicalProperRows h s U:=by
    fin_cases s <;> simp [physicalProperRows,phys]
  have changed:(fun s=>FrozenRead.meanOn ρ u (physicalProperRows h s))=U:=funext fun s=>
    open_patch_common_read e distinct A ma γp u eu stable _ (env s) (sym s)
  have price:=(funded_seven_aperture (μ:=ρ) M mm km am bb kn ap bp rm anchor same
    t tn fee h eh L ln pay (eu.integrable ρ) vi' wp cc vp).2
  rw [changed,wg,wc,wh,pin] at price
  apply le_of_mul_le_mul_left (a:=γ)
  · calc
      γ*(z*‖properThree U-properThree V‖)=(γ*z)*‖properThree U-properThree V‖:=by ring
      _≤(26*L 0*L 1*L 2)*(γ*c*t+γ*(∫x in Bᶜ,u x ∂μ)):=price
      _=γ*((26*L 0*L 1*L 2)*(c*t+∫x in Bᶜ,u x ∂μ)):=by ring
  · exact γp

end YM.Integration.FVA1Physical.Exchange.RoseCut

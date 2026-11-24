import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFundedGaugeMasses

/-! Reinsert the full separately normalized Wilson law. An estimate of its own
tail is charged once; a pure-gauge bond restriction on the regular action need
not be imposed on either physical expectation. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Filter Set RG Wilson Lattice Source
open scoped Classical BigOperators
variable {X:Type*}[MeasurableSpace X]{G:Gauge}{f:Side}

theorem move_read_to_patch (e:Lattice.Edge (Site f))(ne:e.1+Lattice.step e.2≠e.1)
    (D:Set G.El)(dn:D.Nonempty)(B:Set (Config G f))
    (gb:∀a U,gauge (endpointGauge e.1 a) U∈B ↔ U∈B)
    (r:Config G f→ℝ)(gr:∀a U,r (gauge (endpointGauge e.1 a) U)=r U)(t:ℝ)
    (paid:∀x∈openPatch e D∩B,∀y∈openPatch e D∩B,Replica.cap (r x-r y)≤t):
    ∀x∈B,∀y∈B,Replica.cap (r x-r y)≤t:=by
  obtain ⟨b,hb⟩:=dn
  intro x hx y hy
  let a:=fun U:Config G f=>b*(U e)⁻¹
  let move:=fun U:Config G f=>gauge (endpointGauge e.1 (a U)) U
  have enters(U):move U∈openPatch e D:=by
    change (gauge (endpointGauge e.1 (b*(U e)⁻¹)) U) e∈D
    simpa [Lattice.gauge,endpointGauge,ne,mul_assoc] using hb
  have buy:=paid (move x) ⟨enters x,(gb _ x).mpr hx⟩ (move y) ⟨enters y,(gb _ y).mpr hy⟩
  change Replica.cap (r (gauge _ x)-r (gauge _ y))≤t at buy
  rwa [gr,gr] at buy

theorem full_two_tail_seven {μ:Measure X}[SFinite μ] (B:Set X)(mb:MeasurableSet B)
    {k a b:X→ℝ}(km:Measurable k)(am:Measurable a)(bm:Measurable b)
    (kn:∀x,0≤k x)(ap:∀x,0<a x)(bp:∀x,0<b x)(t:ℝ)(tn:0≤t)
    (h:Fin 3→X→ℂ)(env:∀i,Envelope (h i))(L:Fin 3→ℝ)(ln:∀i,0≤L i)(pay:∀i x,‖h i x‖≤L i):
    let r:=fun x=>Real.log (a x)-Real.log (b x)
    let u:=fun x=>k x*a x;let v:=fun x=>k x*b x;let ν:=μ.restrict B;let F:=physicalProperRows h
    let U:=fun i=>FrozenRead.meanOn μ u (F i);let V:=fun i=>FrozenRead.meanOn μ v (F i)
    let z:=∫x,u x ∂μ;let q:=∫x,v x ∂μ;let W:=26*L 0*L 1*L 2
    Integrable u μ→Integrable v μ→0<z→0<q→0<(∫x,u x ∂ν)→0<(∫x,v x ∂ν)→
    (∀x∈B,∀y∈B,Replica.cap (r x-r y)≤t)→
    ‖properThree U-properThree V‖≤W*(((∫x,u x ∂ν)/z)*t+(∫x in Bᶜ,u x ∂μ)/z+(∫x in Bᶜ,v x ∂μ)/q):=by
  intro r u v ν F U V z q W ui vi zp qp cup cvp cap
  let Z:=fun i=>FrozenRead.meanOn ν v (F i)
  have fromU:=(funded_seven_aperture (μ:=μ) B mb km am bm kn ap bp
    (am.log.sub bm.log) 0 (fun _=>by simp only [add_zero];rfl) t tn cap h env L ln pay
    ui vi.integrableOn zp cup cvp).2
  have zero:Replica.cap 0≤0:=by simp [Replica.cap]
  have fromV:=(funded_seven_aperture (μ:=μ) B mb km bm bm kn bp bp (measurable_const (a:=(0:ℝ)))
    0 (fun _=>by simp) 0 le_rfl (fun _ _ _ _=>by simpa only [sub_self] using zero) h env L ln pay
    vi vi.integrableOn qp cvp cvp).2
  have x:‖properThree U-properThree Z‖≤(W*((∫x,u x ∂ν)*t+∫x in Bᶜ,u x ∂μ))/z:=by
    apply (le_div_iff₀ zp).2;rw [mul_comm];exact fromU
  have y:‖properThree Z-properThree V‖≤(W*(∫x in Bᶜ,v x ∂μ))/q:=by
    rw [norm_sub_rev]
    apply (le_div_iff₀ qp).2;rw [mul_comm];simpa only [mul_zero,zero_add] using fromV
  calc
    ‖properThree U-properThree V‖≤‖properThree U-properThree Z‖+‖properThree Z-properThree V‖:=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤(W*((∫x,u x ∂ν)*t+∫x in Bᶜ,u x ∂μ))/z+(W*(∫x in Bᶜ,v x ∂μ))/q:=add_le_add x y
    _=W*(((∫x,u x ∂ν)/z)*t+(∫x in Bᶜ,u x ∂μ)/z+(∫x in Bᶜ,v x ∂μ)/q):=by ring
end YM.Integration.FVA1Physical.Exchange.RoseCut

import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionOverflowProbability

/-! On the complement of the local exceptional set, a single restored
physical singleton splits exactly into the crossed marked pressure and
one additional bounded local scalar test. Nothing is divided by the
retained regional mass in either pressure interface. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal Extra.Histories
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def safeMean (L:Support n)(a:V)(t:T)(w M:ℝ):Config G n→ℂ:=
  (badRegion A L a t w M)ᶜ.indicator (regionRatio A L a t w)

def scalarFraction (L:Support n)(t:T)(U:Config G n):ℂ:=
  (crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L).part C.quiet/(P.activities.gas P.p U:ℂ)

omit [Fintype V] in
theorem safe_mean_test (L Y:Support n)(room:L⊆Y)(a:V)(t:T)(w M:ℝ)(hp:0<M):
    let B:=badRegion A L a t w M
    let q:=safeMean A L a t w M
    Measurable q ∧ UsesFinal P.p.threshold Y q ∧ (∀g U,q (Lattice.gauge g U)=q U) ∧
      (∀U,‖q U‖≤M) ∧ MeasurableSet B ∧ UsesFinal P.p.threshold Y (fun U=>U∈B) ∧
      ∀(g:Site n→G.El)(U:Config G n),(Lattice.gauge g U∈B↔U∈B):=by
  intro B q
  obtain ⟨hm,hu,hg⟩:=left_field_local A L t
  have rm:Measurable (regionRatio A L a t w):=measurable_const.mul
    (((Poly.part_cont _).measurable.comp hm).div ((Poly.part_cont _).measurable.comp hm))
  have bm:MeasurableSet B:=(bad_region_tests A L Y room a t w M hp).1
  have eqs {U V:Config G n}(e:leftField A L t U=leftField A L t V):
      (U∈B ↔ V∈B) ∧ q U=q V:=by
    have same:(U∈B↔V∈B):=by simp only [B,badRegion,singularCut,regionRatio,Set.mem_union,Set.mem_setOf_eq,e]
    refine ⟨same,?_⟩
    by_cases hit:U∈B
    · have hit':=same.mp hit
      simp only [q,safeMean,show badRegion A L a t w M=B from rfl,Set.indicator_of_notMem (show U∉Bᶜ from fun z=>z hit),Set.indicator_of_notMem (show V∉Bᶜ from fun z=>z hit')]
    have uv:U∈Bᶜ:=hit
    have vv:V∈Bᶜ:=fun h=>hit (same.mpr h)
    simp only [q,safeMean,show badRegion A L a t w M=B from rfl,Set.indicator_of_mem uv,Set.indicator_of_mem vv,regionRatio,e]
  have win {U V:Config G n}(fine:Agrees Y U V)(flagsEq:Y∩flags P.p.threshold U=Y∩flags P.p.threshold V):
      leftField A L t U=leftField A L t V:=hu U V (agrees_mono fine (coe_subset.mpr room)) (Attach.narrow _ _ room _ _ flagsEq)
  refine ⟨rm.indicator bm.compl,fun U W links same=>(eqs (win links same)).2,fun g U=>(eqs (hg g U)).2,
    ?_,bm,fun U W links same=>propext (eqs (win links same)).1,fun g U=>(eqs (hg g U)).1⟩
  intro U
  change ‖Bᶜ.indicator _ U‖≤M
  by_cases hit:U∈B
  · rw [Set.indicator_of_notMem (show U∉Bᶜ from fun z=>z hit),norm_zero];exact hp.le
  rw [Set.indicator_of_mem (show U∈Bᶜ from hit)]
  exact le_of_not_gt (fun h=>hit (Or.inr h))

theorem physical_singleton_split (L:Support n)(a:V)(inside:o a∈L)(t:T)(M:ℝ)
    {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)
    (U:Config G n)(live:0<P.eval U):
    let B:=badRegion A L a t (w a) M
    let m:=markerFraction A L a t (w a)
    let q:=safeMean A L a t (w a) M
    let g:=fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U
    g U-q U=B.indicator g U+Bᶜ.indicator m U-q U*scalarFraction A L t U:=by
  intro B m q g
  by_cases hit:U∈B
  · have off:U∉Bᶜ:=fun h=>h hit
    have zero:q U=0:=Set.indicator_of_notMem off _
    rw [zero,zero_mul,Set.indicator_of_mem hit,Set.indicator_of_notMem off,add_zero,sub_zero]
  let l:=leftField A L t U
  let ν:ℂ:=P.activities.gas P.p U
  let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
  let c:=l.part (C.fire a)/l.part C.quiet
  have ok:U∈Bᶜ:=hit
  have left:l.part C.quiet≠0:=fun h=>hit (Or.inl h)
  have raw:=actual_local_singleton A L t U live a inside wp paid en
  have nz:ν≠0:=Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right live (Real.exp_nonneg _)).ne'
  change ν*(originalRaw A t (C.fire a) U-c)=E.part (C.fire a)-c*E.part C.quiet+(if l.part C.quiet=0 then _ else 0) at raw
  rw [if_neg left,add_zero] at raw
  have qq:q U=(w a:ℂ)*c:=Set.indicator_of_mem ok _
  rw [Set.indicator_of_notMem hit,Set.indicator_of_mem ok,zero_add,qq]
  change (w a:ℂ)*originalRaw A t (C.fire a) U-(w a:ℂ)*c=(w a:ℂ)*E.part (C.fire a)/ν-(w a:ℂ)*c*(E.part C.quiet/ν)
  field_simp [nz]
  linear_combination (w a:ℂ)*raw

end YM.Integration.FVA1Physical.Exchange.RoseCut

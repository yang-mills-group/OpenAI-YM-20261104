import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFiledBinCovariance

/-! A bounded local certificate detects both a zero regional scalar and a
large *restored* regional singleton. Its outside term is the original full
scalar, with the exact one-source physical correspondence paid separately. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal Extra.Histories
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def regionRatio (L:Support n)(a:V)(t:T)(w:ℝ)(U:Config G n):ℂ:=
  (w:ℂ)*((leftField A L t U).part (C.fire a)/(leftField A L t U).part C.quiet)

def badRegion (L:Support n)(a:V)(t:T)(w M:ℝ):Set (Config G n):=
  singularCut A t L ∪ {U|M<‖regionRatio A L a t w U‖}

def inverseProbe (L:Support n)(a:V)(t:T)(w M:ℝ)(U:Config G n):ℂ:=
  (badRegion A L a t w M).indicator (fun X=>(M:ℂ)/regionRatio A L a t w X) U

def markerFraction (L:Support n)(a:V)(t:T)(w:ℝ)(U:Config G n):ℂ:=
  (w:ℂ)*(crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L).part (C.fire a)/(P.activities.gas P.p U:ℂ)

omit [Fintype V] in
/-- Both the exceptional-sector indicator and the signed test on its marked
leg are genuine local gauge tests. Rounding or cutting the vacuum is unnecessary. -/
theorem bad_region_tests (L Y:Support n)(room:L⊆Y)(a:V)(t:T)(w M:ℝ)(hp:0<M):
    let B:=badRegion A L a t w M
    let p:=inverseProbe A L a t w M
    let s:=B.indicator (fun _=>(1:ℝ))
    MeasurableSet B ∧ Measurable s ∧ UsesFinal P.p.threshold Y s ∧ (∀g U,s (gauge g U)=s U) ∧
    (∀U,‖s U‖≤1) ∧ Measurable p ∧ UsesFinal P.p.threshold Y p ∧ (∀g U,p (gauge g U)=p U) ∧ ∀U,‖p U‖≤1:=by
  intro B p s
  obtain ⟨lm,ll,lg⟩:=left_field_local A L t
  have ratio:Measurable (regionRatio A L a t w):=measurable_const.mul
    (((Poly.part_cont _).measurable.comp lm).div ((Poly.part_cont _).measurable.comp lm))
  have bm:MeasurableSet B:=(singular_local_test A t L Y room).1.union (measurableSet_lt measurable_const ratio.norm)
  have same {U W:Config G n}(eq:leftField A L t U=leftField A L t W):
      (U∈B ↔ W∈B) ∧ regionRatio A L a t w U=regionRatio A L a t w W:=by
    simp only [B,badRegion,singularCut,regionRatio,Set.mem_union,Set.mem_setOf_eq,eq,and_self,iff_self]
  have short {U W:Config G n}(eq:leftField A L t U=leftField A L t W):s U=s W ∧ p U=p W:=by
    obtain ⟨b,q⟩:=same eq
    by_cases hu:U∈B
    · have hw:=b.mp hu
      simp only [s,p,inverseProbe,show badRegion A L a t w M=B from rfl,Set.indicator_of_mem hu,Set.indicator_of_mem hw,q,and_self]
    have hw:W∉B:=fun h=>hu (b.mpr h)
    simp only [s,p,inverseProbe,show badRegion A L a t w M=B from rfl,Set.indicator_of_notMem hu,Set.indicator_of_notMem hw,and_self]
  have window {U W:Config G n}(links:Agrees Y U W)(mask:Y∩flags P.p.threshold U=Y∩flags P.p.threshold W):
      leftField A L t U=leftField A L t W:=ll U W (agrees_mono links (coe_subset.mpr room)) (Attach.narrow _ _ room _ _ mask)
  refine ⟨bm,measurable_const.indicator bm,fun U W ag mask=>(short (window ag mask)).1,
    fun g U=>(short (lg g U)).1,?_,(measurable_const.div ratio).indicator bm,
    fun U W ag mask=>(short (window ag mask)).2,fun g U=>(short (lg g U)).2,?_⟩
  · intro U;by_cases h:U∈B <;> simp [s,h]
  intro U
  by_cases hit:U∈B
  · change ‖B.indicator (fun X=>(M:ℂ)/regionRatio A L a t w X) U‖≤1
    rw [Set.indicator_of_mem hit]
    rcases hit with zero|large
    · have z:(leftField A L t U).part C.quiet=0:=zero
      simp [regionRatio,z]
    change M<‖regionRatio A L a t w U‖ at large
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hp.le]
    exact (div_le_one (hp.trans large)).mpr large.le
  change ‖B.indicator _ U‖≤1
  rw [Set.indicator_of_notMem hit,norm_zero];norm_num

/-- A positive unit of *actual* fine probability on each bad field, exactly
tested by a bounded local complex phase and bounded real event on the signed
one-source and vacuum crossing. Works on zero and negative cut vacua. -/
theorem bad_field_account (L:Support n)(a:V)(inside:o a∈L)(t:T)(M:ℝ)(hp:0<M)
    {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)
    (U:Config G n)(live:0<P.eval U):
    let B:=badRegion A L a t (w a) M
    let p:=inverseProbe A L a t (w a) M U
    let g:=(w a:ℂ)*originalRaw A t (C.fire a) U
    let ear:=B.indicator (fun _=>(1:ℝ)) U
    M*ear=(p*g).re-(p*markerFraction A L a t (w a) U).re+M*(ear*quietFraction A t L U):=by
  intro B p g ear
  by_cases hit:U∈B
  · have marked:p=(M:ℂ)/regionRatio A L a t (w a) U:=Set.indicator_of_mem hit _
    have ear1:ear=1:=Set.indicator_of_mem hit _
    rw [ear1,mul_one,one_mul,marked]
    rcases hit with zero|large
    · have z:(leftField A L t U).part C.quiet=0:=zero
      rw [singular_crossed_fraction A t L U live wp paid en zero]
      simp only [regionRatio,z,div_zero,mul_zero,zero_mul,Complex.zero_re,sub_zero,zero_add,mul_one]
    let l:=leftField A L t U
    let q:=regionRatio A L a t (w a) U
    let ν:ℂ:=P.activities.gas P.p U
    let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
    change M<‖q‖ at large
    have qz:q≠0:=norm_pos_iff.mp (hp.trans large)
    have lz:l.part C.quiet≠0:=by
      rintro z
      apply qz
      simp only [q,regionRatio,show (leftField A L t U).part C.quiet=0 from z,div_zero,mul_zero]
    have vz:ν≠0:=Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right live (Real.exp_nonneg _)).ne'
    have row:=actual_local_singleton A L t U live a inside wp paid en
    change ν*(originalRaw A t (C.fire a) U-l.part (C.fire a)/l.part C.quiet)=
      E.part (C.fire a)-(l.part (C.fire a)/l.part C.quiet)*E.part C.quiet+(if l.part C.quiet=0 then _ else 0) at row
    rw [if_neg lz,add_zero] at row
    have paidRow:ν*(g-q)=(w a:ℂ)*E.part (C.fire a)-q*E.part C.quiet:=by
      dsimp only [g,q,regionRatio,l] at row ⊢
      linear_combination (w a:ℂ)*row
    have id:(M:ℂ)=(M:ℂ)/q*g-((M:ℂ)/q)*(((w a:ℂ)*E.part (C.fire a))/ν)+(M:ℂ)*(E.part C.quiet/ν):=by
      field_simp [qz,vz]
      linear_combination -(M:ℂ)*paidRow
    have realEq:=congrArg Complex.re id
    have rprod:((M:ℂ)*(E.part C.quiet/ν)).re=M*(E.part C.quiet/ν).re:=by simp [Complex.mul_re]
    rw [Complex.add_re,Complex.sub_re,Complex.ofReal_re,rprod] at realEq
    exact realEq
  have off:p=0:=Set.indicator_of_notMem hit _
  have un:ear=0:=Set.indicator_of_notMem hit _
  simp only [off,un,zero_mul,Complex.zero_re,mul_zero,sub_zero,zero_add]

end YM.Integration.FVA1Physical.Exchange.RoseCut

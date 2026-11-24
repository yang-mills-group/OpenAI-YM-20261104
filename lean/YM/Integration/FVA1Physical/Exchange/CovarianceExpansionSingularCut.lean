import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRegionalProbe

/-! A true probability bound from a signed observable on a nonbare field.
If the local regional vacuum vanishes, the complete scalar crossing equals
the original positive vacuum, including the potentially signed exterior.
This exact local event can therefore be tested by the signed pressure and
charged against a completely unrestricted L² physical path spectator. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker Multi Extra.Histories Extra.Trajectories Comparison.RG02.Cumulants
  Primitives.GCC.Anchor QuadraticLocal
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def singularCut (t:T)(L:Support n):Set (Config G n):={U|(leftField A L t U).part C.quiet=0}

def quietFraction (t:T)(L:Support n)(U:Config G n):ℝ:=
  (((crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L).part C.quiet)/
    (P.activities.gas P.p U:ℂ)).re

omit [Fintype V] in
theorem singular_local_test (t:T)(L Y:Support n)(room:L⊆Y):
    let I:Config G n→ℝ:=(singularCut A t L).indicator (fun _=>1)
    MeasurableSet (singularCut A t L) ∧ Measurable I ∧ UsesFinal P.p.threshold Y I ∧
    (∀g U,I (gauge g U)=I U) ∧ ∀U,‖I U‖≤1:=by
  intro I
  obtain ⟨lm,seen,rot⟩:=left_field_local A L t
  have ev:MeasurableSet (singularCut A t L):=measurableSet_eq_fun ((Poly.part_cont _).measurable.comp lm) measurable_const
  refine ⟨ev,measurable_const.indicator ev,?_,?_,?_⟩
  · intro U X same flagsEq
    have localEq:=seen U X (agrees_mono same (coe_subset.mpr room)) (Attach.narrow _ _ room _ _ flagsEq)
    simp only [I,Set.indicator,Set.mem_setOf_eq,singularCut,localEq]
    split_ifs <;> rfl
  · intro g U
    simp only [I,Set.indicator,singularCut,Set.mem_setOf_eq,rot]
    split_ifs <;> rfl
  intro U
  by_cases hit:U∈singularCut A t L <;> simp [I,hit]

theorem singular_crossed_fraction (t:T)(L:Support n)(U:Config G n)(live:0<P.eval U)
    {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)(hit:U∈singularCut A t L):
    quietFraction A t L U=1:=by
  let l:=leftField A L t U
  let r:=rightField A L t U
  let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
  let O:=univ.filter (fun v=>o v∈L)
  have zero:l.part C.quiet=0:=hit
  have fq:inside C.quiet O=C.quiet:=Subtype.ext (empty_inter O)
  have zq:diff C.quiet O=C.quiet:=Subtype.ext (empty_sdiff O)
  have total:A.gas t U=remainingCash P.activities P.p U (A.K.hard t · U) L+E:=
    crossing_cash_exact P.activities P.p U _ L w wp (filed_actor_stock A wp paid en t U)
  have rows:(remainingCash P.activities P.p U (A.K.hard t · U) L).part C.quiet=l.part (inside C.quiet O)*r.part (diff C.quiet O):=
    regional_rows A L t U wp paid en C.quiet
  have equal:(A.gas t U).part C.quiet=E.part C.quiet:=by
    rw [total,Poly.part_plus,rows,fq,zq,zero,zero_mul,zero_add]
  have base:(A.gas t U).part C.quiet=(P.activities.gas P.p U:ℂ):=Hard.packet_of_quiet A.K t U (Hard.packet_summing _ paid en wp t U)
  have nz:(P.activities.gas P.p U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right live (Real.exp_nonneg _)).ne'
  change (E.part C.quiet/(P.activities.gas P.p U:ℂ)).re=1
  rw [←equal,base,div_self nz,Complex.one_re]

/-- Signed pressure on bounded local gauge observations is enough for the
positive *probability* of this particular original event; no total variation
or sign choice depending on the remote fine fields is assumed. -/
theorem singular_conditional_mass (μ:Measure (Config G n))[IsFiniteMeasure μ](live:∀U,0<P.eval U)
    (t:T)(L Y:Support n)(room:L⊆Y){w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}
    (paid:A.K.Paid w P.p.B e κ)(en:0≤e)(fee:ℝ)
    (pressure:∀f:Config G n→ℝ,Measurable f→UsesFinal P.p.threshold Y f→(∀g U,f (gauge g U)=f U)→
      (∀U,‖f U‖≤1)→|∫U,f U*quietFraction A t L U ∂μ|≤fee):
    μ.real (singularCut A t L)≤fee:=by
  let E:=singularCut A t L
  let I:=E.indicator (fun _=>(1:ℝ))
  obtain ⟨em,im,loc,rot,cap⟩:=singular_local_test A t L Y room
  have billed:=pressure I im loc rot cap
  have exactRead:(fun U=>I U*quietFraction A t L U)=I:=by
    funext U;by_cases hit:U∈E
    · rw [singular_crossed_fraction A t L U (live U) wp paid en hit,mul_one]
    simp [I,hit]
  have money:(∫U,I U ∂μ)=μ.real E:=by
    rw [show I=E.indicator (fun _:Config G n=>(1:ℝ)) from rfl,integral_indicator em,setIntegral_const]
    simp [E]
  rwa [exactRead,money,abs_of_nonneg measureReal_nonneg] at billed

/-- The spectator itself need not be seen inside the box or at the held
date. The only statistical assertion used is a signed local-pressure bill
on the prescribed marginal, and the bound is uniform in all L² spectators. -/
theorem singular_original_spectator {Z:Type*}[MeasurableSpace Z](law:Measure Z)[IsFiniteMeasure law]
    (μ:Measure (Config G n))[IsFiniteMeasure μ](π:Z→Config G n)(pm:Measurable π)(original:Measure.map π law=μ)
    (live:∀U,0<P.eval U)(t:T)(L Y:Support n)(room:L⊆Y){w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}
    (paid:A.K.Paid w P.p.B e κ)(en:0≤e)(fee:ℝ)
    (pressure:∀f:Config G n→ℝ,Measurable f→UsesFinal P.p.threshold Y f→(∀g U,f (gauge g U)=f U)→
      (∀U,‖f U‖≤1)→|∫U,f U*quietFraction A t L U ∂μ|≤fee)
    (H:Z→ℂ)(h2:MemLp H 2 law):
    let D:=π ⁻¹' singularCut A t L
    Integrable (D.indicator H) law ∧ ‖∫z,D.indicator H z ∂law‖≤Real.sqrt fee*Real.sqrt (∫z,‖H z‖^2 ∂law):=by
  intro D
  have ev:MeasurableSet (singularCut A t L):=(singular_local_test A t L Y room).1
  have dm:MeasurableSet D:=ev.preimage pm
  have mass:=singular_conditional_mass A μ live t L Y room wp paid en fee pressure
  have pull:law.real D=μ.real (singularCut A t L):=by
    rw [←original];exact (congrArg ENNReal.toReal (Measure.map_apply pm ev)).symm
  have hi:=h2.indicator dm
  obtain ⟨ent,bill⟩:=support_rms law D dm (D.indicator H) hi (fun z hz=>Set.indicator_of_notMem hz H)
  have sq:(∫z,‖D.indicator H z‖^2 ∂law)≤∫z,‖H z‖^2 ∂law:=by
    apply integral_mono ((memLp_two_iff_integrable_sq_norm hi.1).1 hi) ((memLp_two_iff_integrable_sq_norm h2.1).1 h2)
    intro z
    change ‖D.indicator H z‖^2≤‖H z‖^2
    by_cases x:z∈D
    · rw [Set.indicator_of_mem x]
    rw [Set.indicator_of_notMem x,norm_zero,zero_pow (by norm_num:2≠0)]
    exact sq_nonneg _
  refine ⟨ent,bill.trans ?_⟩
  exact mul_le_mul (Real.sqrt_le_sqrt (pull.le.trans mass)) (Real.sqrt_le_sqrt sq) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end YM.Integration.FVA1Physical.Exchange.RoseCut

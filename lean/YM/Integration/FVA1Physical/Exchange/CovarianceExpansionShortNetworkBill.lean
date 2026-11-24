import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionLocalFailureAlternative
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

/-! A short-support contribution to a separated, signed original hard
cofactor. A correlated exterior remains inside the original joint second
moment. Distinct flagged sites, rather than flags sampled independently,
purchase an explicit event probability on this same original regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset Filter MeasureTheory Lattice RG Wilson Marker Multi Extra.Trajectories Push.AbsoluteSums.Animals
open scoped Classical BigOperators ENNReal
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

def crowd (θ:ℝ)(F:Support n)(m:ℕ):Set (Config G n):=
  ⋃ Z∈F.powersetCard m, {U|Z⊆flags θ U}

theorem crowd_measurable (θ:ℝ)(F:Support n)(m:ℕ):
    MeasurableSet (crowd (G:=G) θ F m):=by
  apply MeasurableSet.iUnion
  intro Z
  apply MeasurableSet.iUnion
  intro _
  have eq:{U:Config G n|Z⊆flags θ U}=⋂z:↥Z,{U|z.val∈flags θ U}:=by
    ext U
    simp only [Set.mem_setOf_eq,Set.mem_iInter,Subtype.forall]
    exact ⟨fun h _ hz=>h hz,fun h _ hz=>h _ hz⟩
  rw [eq]
  exact MeasurableSet.iInter fun z=>(flags_open ..).measurableSet

theorem crowd_bound (μ:Measure (Config G n))[IsFiniteMeasure μ](θ rate:ℝ)
    (rare:∀Z:Support n, μ.real {U|Z⊆flags θ U}≤rate^Z.card)(F:Support n)(m:ℕ):
    μ.real (crowd (G:=G) θ F m)≤(F.card.choose m:ℕ)*rate^m:=by
  let E:=fun Z:Support n=>{U:Config G n|Z⊆flags θ U}
  apply (measureReal_biUnion_finset_le (μ:=μ) (F.powersetCard m) E).trans
  apply (sum_le_sum (g:=fun _=>rate^m) (fun Z hz=>?_)).trans_eq
  · simp
  simpa only [(mem_powersetCard.mp hz).2] using rare Z

theorem support_rms {T:Type*}[MeasurableSpace T](law:Measure T)[IsFiniteMeasure law]
    (E:Set T)(em:MeasurableSet E)(Z:T→ℂ)(z2:MemLp Z 2 law)
    (off:∀t,t∉E → Z t=0):Integrable Z law ∧
    ‖∫t,Z t ∂law‖≤Real.sqrt (law.real E)*Real.sqrt (∫t,‖Z t‖^2 ∂law):=by
  let f:=E.indicator (fun _:T=>(1:ℝ))
  have f2:MemLp f 2 law:=(memLp_const (1:ℝ)).indicator em
  have fpos (t:T):0≤f t:=by by_cases hit:t∈E <;> simp [f,hit]
  have abs (t:T):f t*‖Z t‖=‖Z t‖:=by
    by_cases hit:t∈E
    · simp [f,hit]
    simp [f,hit,off t hit]
  have sq (t:T):f t^2=f t:=by by_cases hit:t∈E <;> simp [f,hit]
  have cash:(∫t,f t^2 ∂law)=law.real E:=by
    simp_rw [sq]
    rw [show f=E.indicator (fun _:T=>(1:ℝ)) from rfl,integral_indicator em,setIntegral_const]
    simp
  have a:MemLp f (ENNReal.ofReal 2) law:=by norm_num;exact f2
  have b:MemLp (fun t=>‖Z t‖) (ENNReal.ofReal 2) law:=by norm_num;exact z2.norm
  have cs:=integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (.of_forall fpos) (.of_forall fun _=>norm_nonneg _) a b
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow,abs,cash] at cs
  exact ⟨z2.integrable (by norm_num), (norm_integral_le_integral_norm _).trans cs⟩

/-- The physical integrand keeps the original scalar gas and all markers,
together with any chosen jointly sampled (and possibly complex) exterior.
Only the sector without a large active actor meeting the local ball is read. -/
def shortReading {T:Type*}(B:Activities G n)(p:BudgetPoint)(K:Config G n→ℕ→Poly C)
    (π:T→Config G n)(Y:T→ℂ)(x:Site n)(k D:ℕ)(s:C.Mode)(t:T):ℂ:=
  if B.gas p (π t)≠0 ∧ ¬LongAt B p (K (π t)) x k D then
    Y t*(connected (((B.gas p (π t):ℂ)⁻¹) • ∑'S,RoseRoster.roster B p (π t) (K (π t)) S)).part s
  else 0

/-- With k=2m short diameters between the two insertions, at least m
different flagged sites lie inside their nominated finite ball. Integrating
that actual signed contribution prices its joint RMS by the square root of
the joint-site rate. The marginal equality is required on the original law. -/
theorem original_short_hearing {T:Type*}[MeasurableSpace T](law:Measure T)[IsFiniteMeasure law]
    (μ:Measure (Config G n))[IsFiniteMeasure μ](π:T→Config G n)(πm:Measurable π)
    (original:Measure.map π law=μ)
    (B:Activities G n)(p:BudgetPoint)(K:Config G n→ℕ→Poly C)
    (o:V→Site n)(carry:∀U (i:ℕ)(r:C.Mode),(K U i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (licensed:∀U i,K U i≠0 → (B.forced i).eligible p.threshold U)
    (K₀:∀U i,(K U i).part C.quiet=(B.K i U:ℂ))
    (w:V→ℝ)(wp:∀v,0<w v)(stock:∀U,Summable fun i=>Poly.price w (K U i))
    (s:C.Mode)(a b:V)(usedA:a∈s.val)(usedB:b∈s.val)(m D:ℕ)
    (separated:2*m*width p D<separation (o a) (o b))(rate:ℝ)
    (rare:∀Z:Support n, μ.real {U|Z⊆flags p.threshold U}≤rate^Z.card)
    (Y:T→ℂ)(paid:MemLp (shortReading B p K π Y (o a) (2*m) D s) 2 law):
    let H:=shortReading B p K π Y (o a) (2*m) D s
    let F:=neighbors (2*m*width p D) (o a)
    Integrable H law ∧ ‖∫t,H t ∂law‖≤Real.sqrt ((F.card.choose m:ℕ)*rate^m)*
      Real.sqrt (∫t,‖H t‖^2 ∂law):=by
  intro H F
  let E:=crowd (G:=G) p.threshold F m
  have em:MeasurableSet E:=crowd_measurable .. 
  have off (t:T)(outside:t∉π ⁻¹' E):H t=0:=by
    change shortReading B p K π Y (o a) (2*m) D s t=0
    unfold shortReading
    split
    next grant =>
      apply mul_eq_zero_of_right
      by_contra val
      have paidSite:=(original_limited_window B p (π t) (K (π t)) o (carry _) (licensed _)
        (K₀ _) grant.1 w wp (stock _) s val a b usedA usedB (2*m) D separated).resolve_left grant.2
      have number:m≤(flags p.threshold (π t)∩F).card:=by dsimp only [F];omega
      obtain ⟨Z,take,count⟩:=Finset.exists_subset_card_eq number
      exact outside (Set.mem_iUnion.mpr ⟨Z,Set.mem_iUnion.mpr
        ⟨mem_powersetCard.mpr ⟨take.trans inter_subset_right,count⟩,take.trans inter_subset_left⟩⟩)
    rfl
  obtain ⟨keep,bill⟩:=support_rms law (π ⁻¹' E) (em.preimage πm) H paid off
  have marginal:law.real (π ⁻¹' E)=μ.real E:=by
    rw [←original]
    exact (congrArg ENNReal.toReal (Measure.map_apply πm em)).symm
  rw [marginal] at bill
  exact ⟨keep,bill.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (crowd_bound μ _ _ rare F m))
    (Real.sqrt_nonneg _))⟩

end YM.Integration.FVA1Physical.Exchange.RoseCut

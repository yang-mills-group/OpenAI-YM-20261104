import YM.Integration.WilsonPhysicalPositionBranchLimits
import Mathlib.Topology.Sequences

/-! On the elected physical Wilson hierarchy every small-radius transition,
uniformly in the bounded radius ratio, approaches a single finite set of
Born symmetries. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionUniformBranches
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionBornCandidates (operator)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)

def change (d:ℕ)(r t:ℝ)(ht:0<t): (Bel C.book).Field d→L[ℂ](Bel C.book).Field d:=
  (Frame.cocycle d J r t ht).toLinearMap.toContinuousLinearMap

private theorem localize {E M:Type*}[NormedAddCommGroup E][ProperSpace E]
    (A:(r t:ℝ)→0<t→E)(menu:Finset M)(U:M→E){c B ε:ℝ}(hc:0<c)(he:0<ε)
    (price:∀ᶠ r in trail,∀t,∀hi:t∈Icc c 1,‖A r t (hc.trans_le hi.1)‖≤B)
    (ear:∀(r t:ℕ→ℝ)(u:ℝ),0<u→Tendsto r atTop trail→Tendsto t atTop (𝓝 u)→
      ∀hi:∀n,t n∈Icc c 1,∀T:E,Tendsto (fun n=>A (r n) (t n) (hc.trans_le (hi n).1)) atTop (𝓝 T)→
        ∃a∈menu,U a=T):
    ∀ᶠ r in trail,∀t,∀hi:t∈Icc c 1,∃a∈menu,‖A r t (hc.trans_le hi.1)-U a‖<ε:=by
  by_contra failed
  obtain ⟨r,hr,deny⟩:=Filter.exists_seq_forall_of_frequently (Filter.not_eventually.mp failed)
  have bad:∀n,∃t:ℝ,∃ ht:t∈Icc c 1,∀a∈menu,ε≤‖A (r n) t (hc.trans_le ht.1)-U a‖:=by
    intro n
    obtain ⟨t,den⟩:=not_forall.mp (deny n)
    obtain ⟨h,den'⟩:=not_forall.mp den
    exact ⟨t,h,fun a ha=>le_of_not_gt (fun e=>den' ⟨a,ha,e⟩)⟩
  choose t hi bad using bad
  let Z(n:ℕ):E:=A (r n) (t n) (hc.trans_le (hi n).1)
  let x(n:ℕ):ℝ×E:=(t n,Z n)
  have kept:∀ᶠ n in atTop,x n∈Icc c 1 ×ˢ Metric.closedBall 0 B:=by
    filter_upwards [hr.eventually price] with n paid
    refine ⟨hi n,?_⟩
    change dist (Z n) 0≤B
    rw [dist_zero_right]
    exact paid (t n) (hi n)
  obtain ⟨⟨u,T⟩,hu,k,hk,conv⟩:=
    (isCompact_Icc.prod (isCompact_closedBall (0:E) B)).tendsto_subseq' kept.frequently
  change Tendsto (fun n=>(t (k n),Z (k n))) atTop (𝓝 (u,T)) at conv
  have ht:Tendsto (fun n=>t (k n)) atTop (𝓝 u):=(continuous_fst.tendsto (u,T)).comp conv
  have hT:Tendsto (fun n=>Z (k n)) atTop (𝓝 T):=(continuous_snd.tendsto (u,T)).comp conv
  obtain ⟨a,ha,eq⟩:=ear (r ∘ k) (t ∘ k) u (hc.trans_le hu.1.1) (hr.comp hk.tendsto_atTop)
    ht (fun n=>hi (k n)) T hT
  obtain ⟨n,hn⟩:=(Metric.tendsto_nhds.mp hT ε he).exists
  rw [←eq,dist_eq_norm] at hn
  exact (not_lt_of_ge (bad (k n) a ha)) hn

private theorem evaluation {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    {A:ℕ→E→L[ℂ]E}{T:E→L[ℂ]E}
    (h:Tendsto A atTop (𝓝 T))(v:E):Tendsto (fun n=>A n v) atTop (𝓝 (T v)):=
  ((ContinuousLinearMap.apply ℂ E v).continuous.tendsto T).comp h

theorem original (lead:Leading F J)(V:Store G)(d:ℕ):∃ menu:Finset (MoveSpace G d),
    ∀(c:ℝ)(hc:0<c)(ε:ℝ),0<ε→∀ᶠ r in trail,∀(t:ℝ)(hi:t∈Icc c 1),
      ∃a∈menu,‖change J d r t (hc.trans_le hi.1)-operator C a‖<ε:=by
  let X:=(Bel C.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  letI : ProperSpace (X→L[ℂ]X):=FiniteDimensional.proper ℂ _
  obtain ⟨menu,ear⟩:=WilsonPhysicalPositionBranchLimits.original F J lead V d
  obtain ⟨B,hB,price⟩:=Frame.comparison F d J lead
  refine ⟨menu,?_⟩
  intro c hc ε he
  apply localize (B:=B) (change J d) menu (operator C) hc he
  · filter_upwards [price c hc] with r paid
    exact fun t hi=>ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB) (paid t hi).1
  intro r t u hu hr ht hi T hT
  have atv(v:X):Tendsto (fun n=>change J d (r n) (t n) (hc.trans_le (hi n).1) v) atTop (𝓝 (T v)):=
    evaluation (E:=X) (A:=fun n=>change J d (r n) (t n) (hc.trans_le (hi n).1)) (T:=T) hT v
  obtain ⟨a,ha,eq⟩:=ear hc hu hr ht (Eventually.of_forall hi) (fun n=>hc.trans_le (hi n).1) T.toLinearMap atv
  refine ⟨a,ha,ContinuousLinearMap.ext fun v=>?_⟩
  exact congrArg (fun U:X→ₗ[ℂ]X=>U v) eq

end YM.Integration.WilsonPhysicalPositionUniformBranches
end

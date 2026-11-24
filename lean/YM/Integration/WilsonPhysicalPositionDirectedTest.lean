import YM.Integration.WilsonPhysicalPositionDirectedReturn

/-! The real two-home displacement equals twice the Born self less twice one
directed physical overlap, up to an error uniform over bounded ratios. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionDirectedTest
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open PertExtension.Rigidity.Positive
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPhysicalPositionReflectedReturn (reading)
open WilsonPhysicalPositionDirectedReturn (cross)
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

def baseline {d:ℕ}(v:D d):ℝ:=positive C.labels (hierarchy C.labels) v v

private theorem expand {d:ℕ}(v z:D d)(h:baseline z=baseline v):
    baseline (v-z)+2*positive C.labels (hierarchy C.labels) z v-2*baseline v=0:=by
  unfold baseline at *
  simp only [map_sub,LinearMap.sub_apply]
  rw [WilsonPhysicalPositionBornInner.symmetric v z,h]
  ring

def residue {d:ℕ}(v:D d)(r t:ℝ):ℝ:=
  reading F J v r t+2*cross F J v r t-2*baseline v

private theorem scalarLimit (lead:Leading F J){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))(v:D d):
    Tendsto (fun i=>residue F J v (r i) (t i)) l (𝓝 0):=by
  have read:=WilsonPhysicalPositionReflectedReturn.original F J lead hr hu ht pos Z conv v
  obtain ⟨mix,self⟩:=WilsonPhysicalPositionDirectedReturn.original F J lead hr hu ht pos Z conv v
  let A:=positive (d:=d) C.labels (hierarchy C.labels)
  have coeff (z:D d):A (v-z) (v-z)=A v v-A z v-A z v+A z z:=by
    dsimp only [A]
    simp only [map_sub,LinearMap.sub_apply]
    rw [WilsonPhysicalPositionBornInner.symmetric (C:=C) (d:=d) v z]
    ring
  have bill := (read.add (tendsto_const_nhds (x:= (2:ℝ)) |>.mul mix)).sub
    (tendsto_const_nhds (x:=2 * baseline (C:=C) (d:=d) v))
  rw [coeff (Z v),self] at bill
  conv at bill =>
    arg 3; arg 1
    simp only [A,baseline]
    ring_nf
  exact bill

private theorem overInterval {E:Type*}[NormedAddCommGroup E][ProperSpace E]
    (A:(r t:ℝ)→0<t→E)(s:ℝ→ℝ→ℝ){c B ε:ℝ}(hc:0<c)(he:0<ε)
    (bounded:∀ᶠr in trail,∀t,∀p:t∈Icc c 1,‖A r t (hc.trans_le p.1)‖≤B)
    (pay:∀(r t:ℕ→ℝ){u:ℝ},Tendsto r atTop trail→0<u→Tendsto t atTop (𝓝 u)→
      ∀(pos:∀n,0<t n)(T:E),Tendsto (fun n=>A (r n) (t n) (pos n)) atTop (𝓝 T)→
      Tendsto (fun n=>s (r n) (t n)) atTop (𝓝 0)):
    ∀ᶠ r in trail,∀t∈Icc c 1,|s r t|<ε:=by
  by_contra bad
  obtain ⟨r,hr,fail⟩:=Filter.exists_seq_forall_of_frequently (Filter.not_eventually.mp bad)
  have denied(n:ℕ):∃t∈Icc c 1,ε≤|s (r n) t|:=by
    obtain ⟨t,ht⟩:=not_forall.mp (fail n)
    obtain ⟨h,no⟩:=not_forall.mp ht
    exact ⟨t,h,le_of_not_gt no⟩
  choose t hi deny using denied
  let a(n:ℕ):E:=A (r n) (t n) (hc.trans_le (hi n).1)
  have kept:∀ᶠ n in atTop,(t n,a n)∈Icc c 1 ×ˢ Metric.closedBall 0 B:=by
    filter_upwards [hr.eventually bounded] with n paid
    exact ⟨hi n,by simpa only [Metric.mem_closedBall,dist_zero_right] using paid (t n) (hi n)⟩
  obtain ⟨⟨u,T⟩,hu,k,hk,conv⟩:=(isCompact_Icc.prod (isCompact_closedBall (0:E) B)).tendsto_subseq' kept.frequently
  change Tendsto (fun n=>(t (k n),a (k n))) atTop (𝓝 (u,T)) at conv
  have ht:Tendsto (t ∘ k) atTop (𝓝 u):=(continuous_fst.tendsto (u,T)).comp conv
  have hT:Tendsto (a ∘ k) atTop (𝓝 T):=(continuous_snd.tendsto (u,T)).comp conv
  have lim:=pay (r ∘ k) (t ∘ k) (hr.comp hk.tendsto_atTop) (hc.trans_le hu.1.1) ht
    (fun n=>hc.trans_le (hi (k n)).1) T hT
  have upper:ε≤|(0:ℝ)|:=ge_of_tendsto lim.abs (.of_forall fun n=>deny (k n))
  exact (not_le_of_gt he) (by simpa only [abs_zero] using upper)

private theorem evaluated {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    {A:ℕ→E→L[ℂ]E}{T:E→L[ℂ]E}(h:Tendsto A atTop (𝓝 T))(v:E):
    Tendsto (fun n=>A n v) atTop (𝓝 (T v)):=((ContinuousLinearMap.apply ℂ E v).continuous.tendsto T).comp h

theorem comparison (lead:Leading F J){d:ℕ}(v:D d){c:ℝ}(hc:0<c){ε:ℝ}(he:0<ε):
    ∀ᶠ r in trail,∀t∈Icc c 1,|reading F J v r t+2*cross F J v r t-2*baseline v|<ε:=by
  let X:=D d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  letI : ProperSpace (X→L[ℂ]X):=FiniteDimensional.proper ℂ _
  obtain ⟨B,hB,price⟩:=Frame.comparison F d J lead
  change ∀ᶠ r in trail,∀t∈Icc c 1,|residue F J v r t|<ε
  apply overInterval (E:=X→L[ℂ]X) (B:=B) (change J d) (residue F J v) hc he
  · filter_upwards [price c hc] with r paid
    exact fun t hi=>ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB) (paid t hi).1
  intro r t u hr hu ht pos T hT
  have acts(w:X):Tendsto (fun n=>change J d (r n) (t n) (pos n) w) atTop (𝓝 (T w)):=
    evaluated (E:=X) (A:=fun n=>change J d (r n) (t n) (pos n)) (T:=T) hT w
  exact scalarLimit F J lead hr hu ht pos T.toLinearMap acts v

theorem original (lead:Leading F J)(V:Store G)(d:ℕ):
    ∃v:D d,WilsonPhysicalPositionAdmissible.real C d v=v ∧ ∃a:ℝ,0<a ∧
      ((∀ᶠ r in trail,∀t∈Icc (1/2:ℝ) 1,baseline v-a≤cross F J v r t)→
       ∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform J d c):=by
  obtain ⟨v,hv,γ,hγ,apply⟩:=WilsonPhysicalPositionHalfRange.original F J lead V d
  refine ⟨v,hv,γ/4,by linarith only [hγ],?_⟩
  intro paid
  apply apply
  have err:=comparison F J lead v (c:=1/2) (by norm_num) (ε:=γ/2) (by linarith only [hγ])
  filter_upwards [paid,err] with r lower avg t ht
  have h1:=lower t ht
  have h2:=(abs_lt.mp (avg t ht)).2
  linarith only [h1,h2]

end YM.Integration.WilsonPhysicalPositionDirectedTest
end

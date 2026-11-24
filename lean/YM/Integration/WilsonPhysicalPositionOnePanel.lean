import YM.Integration.WilsonPhysicalPositionReflectedReturn

/-! A single real reflected physical measurement to fixed precision identifies
the true scale transition uniformly on each compact interval of ratios. Its
field and precision are chosen before the interval or either radius. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionOnePanel
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionBornCandidates (operator)
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPhysicalPositionReflectedReturn (reading)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

private theorem outside {E:Type*}[NormedAddCommGroup E][ProperSpace E]
    (A:(r t:ℝ)→0<t→E)(U:E){c B ε:ℝ}(hc:0<c)(he:0<ε)
    (price:∀ᶠ r in trail,∀t,∀hi:t∈Icc c 1,‖A r t (hc.trans_le hi.1)‖≤B)
    (bad:¬∀ᶠ r in trail,∀t,∀hi:t∈Icc c 1,‖A r t (hc.trans_le hi.1)-U‖<ε):
    ∃r t:ℕ→ℝ,∃u:ℝ,∃T:E,Tendsto r atTop trail ∧ 0<u ∧ Tendsto t atTop (𝓝 u) ∧
      ∃hi:∀n,t n∈Icc c 1,Tendsto (fun n=>A (r n) (t n) (hc.trans_le (hi n).1)) atTop (𝓝 T) ∧ T≠U:=by
  obtain ⟨r,hr,fail⟩:=Filter.exists_seq_forall_of_frequently (Filter.not_eventually.mp bad)
  have denied(n:ℕ):∃t:ℝ,∃hi:t∈Icc c 1,ε≤‖A (r n) t (hc.trans_le hi.1)-U‖:=by
    obtain ⟨t,no⟩:=not_forall.mp (fail n)
    obtain ⟨hi,no⟩:=not_forall.mp no
    exact ⟨t,hi,le_of_not_gt no⟩
  choose t hi deny using denied
  let a(n:ℕ):E:=A (r n) (t n) (hc.trans_le (hi n).1)
  have kept:∀ᶠ n in atTop,(t n,a n)∈Icc c 1 ×ˢ Metric.closedBall 0 B:=by
    filter_upwards [hr.eventually price] with n paid
    exact ⟨hi n,by simpa only [Metric.mem_closedBall,dist_zero_right] using paid (t n) (hi n)⟩
  obtain ⟨⟨u,T⟩,hu,k,hk,conv⟩:=(isCompact_Icc.prod (isCompact_closedBall (0:E) B)).tendsto_subseq' kept.frequently
  change Tendsto (fun n=>(t (k n),a (k n))) atTop (𝓝 (u,T)) at conv
  have hT:Tendsto (fun n=>a (k n)) atTop (𝓝 T):=(continuous_snd.tendsto (u,T)).comp conv
  refine ⟨r ∘ k,t ∘ k,u,T,hr.comp hk.tendsto_atTop,hc.trans_le hu.1.1,(continuous_fst.tendsto (u,T)).comp conv,
    fun n=>hi (k n),hT,?_⟩
  rintro rfl
  obtain ⟨n,hn⟩:=(Metric.tendsto_nhds.mp hT ε he).exists
  rw [dist_eq_norm] at hn
  exact (not_lt_of_ge (deny (k n))) hn

private theorem apply_limit {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    {A:ℕ→E→L[ℂ]E}{T:E→L[ℂ]E}(h:Tendsto A atTop (𝓝 T))(v:E):
    Tendsto (fun n=>A n v) atTop (𝓝 (T v)):=((ContinuousLinearMap.apply ℂ E v).continuous.tendsto T).comp h

private theorem accounted {d:ℕ}(v:D d)(a:MoveSpace G d)(T:D d→L[ℂ]D d)(eq:operator C a=T):
    WilsonPhysicalPositionRealBranchPanel.fee C v a=PertExtension.Rigidity.Positive.positive C.labels (hierarchy C.labels)
      (v-T.toLinearMap v) (v-T.toLinearMap v):=by
  have same:T.toLinearMap v=operator C a v:=by
    rw [eq]
    rfl
  unfold WilsonPhysicalPositionRealBranchPanel.fee
  rw [same]

theorem original (lead:Leading F J)(V:Store G)(d:ℕ):
    ∃v:D d,WilsonPhysicalPositionAdmissible.real C d v=v ∧ ∃γ:ℝ,0<γ ∧ ∀(c:ℝ)(hc:0<c),
    (∀ᶠ r in trail,∀t∈Icc c 1,reading F J v r t≤γ)→∀ε:ℝ,0<ε→
    ∀ᶠ r in trail,∀(t:ℝ)(ht:t∈Icc c 1),‖change J d r t (hc.trans_le ht.1)-ContinuousLinearMap.id ℂ (D d)‖<ε:=by
  let X:=D d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  letI : ProperSpace (X→L[ℂ]X):=FiniteDimensional.proper ℂ _
  obtain ⟨menu,ear⟩:=WilsonPhysicalPositionBranchLimits.original F J lead V d
  obtain ⟨v,real,γ,hγ,gap⟩:=WilsonPhysicalPositionRealBranchPanel.original C menu
  refine ⟨v,real,γ,hγ,?_⟩
  intro c hc paid ε he
  obtain ⟨B,hB,price⟩:=Frame.comparison F d J lead
  by_contra no
  have bounded:∀ᶠ r in trail,∀t,∀ht:t∈Icc c 1,‖change J d r t (hc.trans_le ht.1)‖≤B:=by
    filter_upwards [price c hc] with r ready
    exact fun t ht=>ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB) (ready t ht).1
  obtain ⟨r,t,u,T,hr,hu,ht,hi,conv,off⟩:=outside (change J d) (ContinuousLinearMap.id ℂ X) hc he bounded no
  let pos(n:ℕ):0<t n:=hc.trans_le (hi n).1
  have acts(w:X):Tendsto (fun n=>Frame.cocycle d J (r n) (t n) (pos n) w) atTop (𝓝 (T w)):=
    apply_limit (E:=X) (A:=fun n=>change J d (r n) (t n) (pos n)) conv w
  obtain ⟨a,ha,hat⟩:=ear hc hu hr ht (.of_forall hi) pos T.toLinearMap acts
  have equal:operator C a=T:=ContinuousLinearMap.ext fun w=>congrArg (fun Q:X→ₗ[ℂ]X=>Q w) hat
  have actual:=WilsonPhysicalPositionReflectedReturn.original F J lead hr hu ht pos T.toLinearMap acts v
  have low:WilsonPhysicalPositionRealBranchPanel.fee C v a≤γ:=by
    rw [accounted (C:=C) v a T equal]
    exact le_of_tendsto actual ((hr.eventually paid).mono fun n hn=>hn (t n) (hi n))
  have high:4*γ≤WilsonPhysicalPositionRealBranchPanel.fee C v a:=gap a ha (fun e=>off (equal.symm.trans e))
  have tooSmall:γ<4*γ:=by linarith only [hγ]
  exact (not_le_of_gt tooSmall) (high.trans low)

end YM.Integration.WilsonPhysicalPositionOnePanel
end

import YM.AveragedStep.Parcel.Near
import YM.AveragedStep.Chart.Score
/-!
Exact localization of the posterior score at one free link under its mask.
No smooth hypothesis on likelihood off the gate or independent evaluation
of tags in overlapping Gram queries. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Function Filter Lattice Wilson RG Loops Tree MeasureTheory Precision
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal
variable {G:Gauge} {c f:Side}{S:StepData c f} {A:ChartRatio G}
variable (F:Forest S.ratio) (Q:Cuff S.patch S.kernel A)
def pick (p:Parcel c f)(X:Rim c f→G.Color)(i:Interior S.patch):G.Color:= (hook S p i).elim 0 X
def close(e:Rim c f)(X:Rim c f→G.Color):ℝ:=
   ∑ p∈owners S e,chip S.patch S.kernel (sort p) (canon S.patch) (pick (S:=S) p X)
-- canon maybe ns AveragedStep
def ramp (v:F.Free)(U:F.Slice G)(x:G.El):F.Slice G:=update U v x
lemma aboard_ramp (b:Site c)(v:F.Free)(U:F.Slice G)(V:Config G c)(x:G.El):
    aboard F b (ramp F v U x,V)=update (aboard F b (U,V)) (.inl v.val) x:=by
  funext j; rcases v with ⟨q,h⟩; rcases j with i|i
  · change F.drape _ i= _
    by_cases he:i=q; · subst i; rw [show F.drape _ _=_ from F.off_tree (ramp F ⟨q,h⟩ U x) ⟨q,h⟩]; unfold ramp; rw [update_self,update_self]
    rw [update_of_ne (by simpa using he)]; change F.drape _ i = F.drape _ _
    by_cases hx:i∈F.trunks; · exact (F.on_tree _ ⟨i,hx⟩).trans (F.on_tree _ ⟨i,hx⟩).symm
    rw [show F.drape _ i=_ from F.off_tree (ramp F ⟨q,h⟩ U x) ⟨i,hx⟩,show F.drape U i=_ from F.off_tree U ⟨i,hx⟩]; exact update_of_ne (by simpa using he) _ _
  exact (update_of_ne (by simp) _ _).symm
-- gauge accessor Cuff
private lemma core_rest (w:G.El)(h:w∈Q.core):G.lieExp (Q.logC w)=w:=by
  obtain ⟨t,ht,rfl⟩:=h; rw [Q.wind_id (by simpa using ht)]

variable (b:Site c) (j:F.Free)
def outerGate (p:TopologyQ F G):ℝ:= ∏ i∈(home S (.inl j.val)).erase (.inl j.val), Q.ticket (aboard F b p i)
lemma outer_same (U:F.Slice G)(V:Config G c)(z:G.El): outerGate F Q b j (ramp F j U z,V)=outerGate F Q b j (U,V):=by
 unfold outerGate; rw [aboard_ramp]; apply Finset.prod_congr rfl; intro i hi; rw [update_of_ne (Finset.ne_of_mem_erase hi)]
private def rail (u:TopologyQ F G)(x:G.Color):Rim c f→G.Color:=update (Q.logC ∘ aboard F b u) (.inl j.val) x
private lemma small_neighbor (p:TopologyQ F G) (hp:outerGate F Q b j p≠0)
    {z:Rim c f}(hz:z∈home S (.inl j.val))(he:z≠ .inl j.val): Q.ticket (aboard F b p z)≠0:=by
 intro h; exact hp (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨he,hz⟩) h)

private lemma tcover(a:Parcel c f)(ha:a∈owners S (Sum.inl j.val))(U:F.Slice G)(V:Config G c)(x:G.Color)(h: ‖x‖≤ 3*Q.width)
    (he:outerGate F Q b j (U,V)≠0):
    let p:=rail F Q b j (U,V) x
    let Y:=aboard F b (ramp F j U (G.lieExp x),V)
    gathers S a Y=(fun t=>G.lieExp (pick (S:=S) a p t)) ∧ ‖pick (S:=S) a p‖≤3*Q.width:=by
 intro p Y
 have he(i)(hz:i∈land S a): Y i=G.lieExp (p i) ∧ ‖p i‖≤ 3*Q.width:=by
    by_cases ht:i= Sum.inl j.val
    · subst i; unfold Y p rail; rw [aboard_ramp,update_self,update_self]; exact ⟨rfl,h⟩
    obtain ⟨hz₀,hq⟩:=Q.detected (small_neighbor F Q b j (U,V) he (home_owner S ha hz) ht)
    unfold Y p rail; rw [aboard_ramp,update_of_ne ht,update_of_ne ht]; change _= G.lieExp (Q.logC _) ∧ ‖Q.logC _‖≤ _
    exact ⟨(core_rest Q _ hz₀).symm,hq.le.trans (by linarith [Q.active])⟩
 have hp(t:Interior S.patch):gathers S a Y t=G.lieExp (pick (S:=S) a p t) ∧ ‖pick (S:=S) a p t‖ ≤ 3*Q.width:=by
    unfold gathers aim pick; cases hx:hook S a t; · constructor; exact G.mat_lieExp_zero.symm; simp [Option.elim,(by linarith [Q.active] : 0≤3*Q.width)]
    next i => exact he i (land_mem S hx)
 exact ⟨funext fun i=> (hp i).1, (pi_norm_le_iff_of_nonneg (by linarith [Q.active])).mpr fun i=> (hp i).2⟩

private lemma attaches (U:F.Slice G)(V:Config G c)(x:G.Color)(h:‖x‖ ≤3*Q.width)
    (he:outerGate F Q b j (U,V)≠0)(a:Parcel c f)(ha:a∈ owners S (.inl j.val))(t:S.Choices):
    let Z:=rail F Q b j (U,V) x
    let p:=pick (S:=S) a Z
    let Y:Board G c f:=(F.drape (ramp F j U (G.lieExp x)),setGauge b V)
    temperature S t a Y=chip S.patch S.kernel (sort a) (canon S.patch) p ∧ marked S t a Y=numberChip S.patch S.kernel (sort a) (leads S t a) (0:Vectors S.patch G):=by
 intro Z p Y
 unfold temperature marked
 change costume S.patch S.kernel (sort a) (leads S t a) (gathers S a (aboard F b (ramp F j U (G.lieExp x),V)))= _ ∧ mark S.patch S.kernel (sort a) (leads S t a) (gathers S a (aboard F b (ramp F j U (G.lieExp x),V)))= _
 obtain ⟨hY,hK⟩:=tcover F Q b j a ha U V x h he
 rw [hY]; change chip S.patch S.kernel (sort a) (leads S t a) p=_ ∧ numberChip S.patch S.kernel (sort a) (leads S t a) p=_
 exact Q.agree _ _ _ hK
lemma remains (p:Parcel c f)(hp:p∉owners S (.inl j.val)) (U:F.Slice G)(V:Config G c)(x:G.El):
    gathers S p (aboard F b (ramp F j U x,V))=gathers S p (aboard F b (U,V)):=by
 rw [aboard_ramp]; funext i; unfold gathers aim; cases he:hook S p i; rfl
 next t=> exact update_of_ne (show t≠ .inl j.val from by rintro rfl; exact hp (own_member S (land_mem S he))) _ _

set_option quotPrecheck false
local notation "N"=> Fintype.card (Edge (Site c))
private lemma by_tag (hS:S.patch.Branches S.kernel G)(β:ℝ)(U:F.Slice G)(V:Config G c)
    (he:outerGate F Q b j (U,V)≠0)(t:S.Choices) : ∃ k:ℝ,∀ x:G.Color,‖x‖≤3*Q.width→
      let Y:Board G c f:=(F.drape (ramp F j U (G.lieExp x)), setGauge b V)
      weightQ S β t Y*bare β Y.1=k*Real.exp (-β* close (S:=S) (Sum.inl j.val) (rail F Q b j (U,V) x)):=by
  let e:Rim c f:=.inl j.val
  let s:=owners S e
  let B:Board G c f:=(F.drape U,setGauge b V)
  let L:=∑ p∈sᶜ,temperature S t p B
  let q(p:Parcel c f):= numberChip S.patch S.kernel (sort p) (leads S t p) (0:Vectors S.patch G)
  refine ⟨(S.penaltyZ β G)⁻¹^(N)*((∏ p∈s,q p)*∏ p∈sᶜ,marked S t p B)*Real.exp (-β*L),fun x hx=> ?_⟩
  intro Y
  rw [invoice S hS]
  have ht (p:Parcel c f)(h:p∉s):temperature S t p Y=temperature S t p B∧ marked S t p Y=marked S t p B:=by
    unfold temperature marked
    have hf:= remains F b j p h U V (G.lieExp x)
    unfold aboard dr at hf; rw [show gathers S p (Sum.elim Y.1 Y.2)=gathers S p (Sum.elim B.1 B.2) from hf]; exact ⟨rfl,rfl⟩
  let P(p):=chip S.patch S.kernel (sort p) (canon S.patch) (pick (S:=S) p (rail F Q b j (U,V) x))
  have hv (p:Parcel c f)(h:p∈s): temperature S t p Y=P p ∧ marked S t p Y=q p:= attaches F Q b j U V x hx he p h t
  rw [← Finset.prod_mul_prod_compl s (fun p=> marked S t p Y),← Finset.sum_add_sum_compl s (fun p=>temperature S t p Y),mul_add,Real.exp_add]
  have hX : ∑ p∈s, temperature S t p Y= ∑ p∈s,P p:=Finset.sum_congr rfl fun p hp=> (hv p hp).1
  rw [hX,show ∑ p∈sᶜ,temperature S t p Y=L from Finset.sum_congr rfl fun p hp=> (ht p (Finset.mem_compl.mp hp)).1,
    show (∏ p∈s,marked S t p Y)=∏ p∈s,q p from Finset.prod_congr rfl fun p hp=> (hv p hp).2,
    show (∏ p∈sᶜ, marked S t p Y)=∏ p∈sᶜ, marked S t p B from Finset.prod_congr rfl fun p hp=> (ht p (Finset.mem_compl.mp hp)).2]
  change _ * _ * (_ * _) = _ * Real.exp (-β*∑ p∈s,P p); ring
lemma by_law (hS:S.patch.Branches S.kernel G)(β:ℝ)(U:F.Slice G)(V:Config G c)
    (he:outerGate F Q b j (U,V)≠0) : ∃ k:ℝ,∀ x:G.Color,‖x‖≤3*Q.width→
      assay F β b (ramp F j U (G.lieExp x),V)=k*Real.exp (-β* close (S:=S) (Sum.inl j.val) (update (Q.logC ∘ aboard F b (U,V)) (Sum.inl j.val) x)):=by
  choose k hk using (by_tag F Q b j hS β U V he)
  refine ⟨∑ i,k i,fun x hx=> ?_⟩
  unfold assay StepData.density; rw [Finset.sum_mul,Finset.sum_mul]; exact Finset.sum_congr rfl fun i _=>hk i x hx
end YM.AveragedStep

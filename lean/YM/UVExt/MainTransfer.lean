import YM.UVExt.Slab

/-! Keep the same branch and true installed low lift through one stencil comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths.Slab
open Function RG Precision Wilson Lattice Bid Exterior Laurent Filter Set Matrix Bloch Tree Tensor
open Work.F03 Work.F04
open scoped Topology ContDiff Classical
set_option linter.unusedSectionVars false
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {p r : Clip} {t : S.Choices}
    {U R : ℕ→PathData G} {η} {ρ : ℕ→fieldDir G c 1 → AxisChart G F}
    {Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ} (L : Slab F U R p r t ρ η Y)
variable {U' R' η' ρ' Y'} (V : Slab F U' R' p r t ρ' η' Y')

lemma solves_slab (v : Dir G c) : ∀ᶠ i in atTop, Optimizes (L.inFT i) v (fun s=>ρ i (s • v)) := by
  filter_upwards [L.critical] with i hi
  let g (s : ℝ) := s • v
  have hg : Tendsto g (𝓝 0) (𝓝 0) := by simpa only [g,zero_smul] using (show Continuous g from continuous_id.smul continuous_const).continuousAt (x:=0) |>.tendsto
  have ht := hi.2.2 t
  exact ⟨by simp [hi.1],((show ContDiffAt ℝ ω (ρ i) (g 0) by simpa only [g,zero_smul] using hi.2.1).comp 0 (show ContDiffAt ℝ ω g 0 from contDiffAt_id.smul contDiffAt_const)),
    ht.1,hg.eventually <| ht.2.mono fun z hz => hz.fderiv⟩

lemma faster (X : ChartVars F G) : HasDerivAt (fun y:ℝ=>axis L (y • X)) (stretch F X) 0 := by
  let g (y:ℝ):= Work.F03.inclusion F (y • X)
  obtain hh := Push.side (Work.F03.inclusion F) ((inclusion_smooth _).differentiableAt (by simp)) X
  exact (by simpa only [inclusion_deriv (S:=S)] using! hh.snd)

include L in
lemma pairedX (v : Dir G c) {z : ChartVars F G} (ht : Tendsto (fun i:ℕ=>fish 1 (paired v fun s=> ρ i (s • v))) atTop (𝓝 z)) : Tendsto (fun i=> (v,relative F (Y i) v)) atTop (𝓝 z) := by
    refine ht.congr' ((L.critical.and L.tangent).mono fun i ⟨hi,hk⟩=> (congr_fun iteratedDeriv_one 0).trans <| (paired_rate _ _ ?_).trans (congr_arg (fun x=>(v,x)) (hk v).deriv))
    exact ((show ContDiffAt ℝ ω (ρ i) ((0:ℝ) • v) by simpa only [zero_smul] using hi.2.1).comp (f:= (fun s:ℝ=>s • v)) 0 (show ContDiffAt ℝ ω (fun t:ℝ=>t • v) 0 from contDiffAt_id.smul contDiffAt_const)).of_le le_top


section transfer
variable {W₁ W₂ Z₁ Z₂ : Shadow G} {s₁ s₂ A₁ A₂ c₁ c₂ t₁ t₂ C₁ C₂ B₁ B₂ : ℝ} (H : Passing U W₁ s₁ A₁ c₁ p) (P : Passing U' W₂ s₂ A₂ c₂ p)
variable {q : ℕ} (hq : 1≤q)
include H P hq
-- `X` need not itself be an anchored tangent family.
lemma unstationed (X : ChartVars F G) (hh : Junction (inFine L) (inFine V) (q-1))
    {A B} (hA : Tendsto (spray L.inFT q) atTop (𝓝 A)) (hB : Tendsto (spray V.inFT q) atTop (𝓝 B)) :
    discrep A B X = discrep (H.planeTensor f q) (P.planeTensor f q) (stretch F X) := by
  let g (t : ℝ) := (Work.F03.axisLog F) (t • X)
  let k (t : ℝ) := t • X
  let t' := L.tail ∘ k
  have hk : ContDiffAt ℝ ∞ k 0 := contDiffAt_id.smul contDiffAt_const
  have he : ContDiffAt ℝ ∞ g 0 := by
     change ContDiffAt ℝ ∞ (Prod.snd ∘ (Work.F03.inclusion F) ∘ k) 0; exact contDiffAt_snd.comp _ ((show ContDiffAt ℝ ∞ (Work.F03.inclusion F) (k 0) by simpa only [k,zero_smul] using (inclusion_smooth F).of_le (show ∞≤ω from le_top)).comp 0 hk)
  let W := fun i=>fish i g
  have hg : Pinned (fun _ : ℕ=>g) := Eventually.of_forall fun _=> by unfold g; simp only [zero_smul]; exact congr_arg Prod.snd (inclusion_zero _)
  have ht {M : ℕ→PathData G} {P : ℕ→PathData G} {Y ρ qη} (L : Slab F M P p r t ρ qη Y) (h₁ : lucid (inFine L)) : ∀ᶠ i in atTop, Tensor.diagonal (spray (inFT L) q i) X= fish q (inFine L i ∘ g)+ fish q t' := by
     filter_upwards [h₁,L.first_flow] with i hi hr
     have hg' : g 0=0 := by
       unfold g; simp only [zero_smul]; exact congr_arg Prod.snd (inclusion_zero (G:=G) F)
     have hf : ContDiffAt ℝ (↑q) (inFine L i ∘ g) 0 := ((show ContDiffAt ℝ (q:ℕ∞ω) (inFine L i) (g 0) from hg'.symm ▸ hi.of_le (finite_cap _)).comp 0 (he.of_le (finite_cap _)))
     have h2 : ContDiffAt ℝ q t' 0 := ((show ContDiffAt ℝ ∞ (L.tail) (k 0) by simpa only [k,zero_smul] using (L.tail_flow h₁)).comp 0 hk).of_le (finite_cap _)
     change Tensor.diagonal (spray (inFT L) q i) X = fish q (inFine L i ∘ g)+ fish q t'
     rw [← ray_tag _ (hr.of_le (finite_cap _))]
     change fish q _= _
     change iteratedDeriv q _ _= iteratedDeriv q _ _ + iteratedDeriv q _ _; rw [←iteratedDeriv_add hf h2]; exact (EventuallyEq.iteratedDeriv (by
       filter_upwards [hk.continuousAt.tendsto.eventually (show _ ∈ 𝓝 (k 0) by unfold k; rw [zero_smul]; exact L.restored i)] with t ht
       change inFT L i (k t)=_; rw [ht]; rfl) q).eq_of_nhds
  let F₁ := H.planeTensor f q
  let F₂ := P.planeTensor f q
  have HA := H.mainLimit f q |>.1
  have HB := P.mainLimit f q |>.1
  have hw := faa_transfer (f:=inFine L) hh hq (H.groomed f) (P.groomed f) (e:=fun _=>g) (e':=fun _=>g) (Eventually.of_forall fun _=>he) (Eventually.of_forall fun _=>he) hg hg HA HB (X:=W) (fun m _=>⟨tendsto_const_nhds,tendsto_const_nhds⟩) (fun c hc=>Or.inl c.partSize_le)
  have hU : Tendsto (fun i=> discrep (spray L.inFT q i) (spray V.inFT q i) X) atTop (𝓝 (discrep A B X)) := (view_cont.continuousAt.tendsto.comp (hA.prodMk_nhds (tendsto_const_nhds (x:=fun _=> X)))).sub (view_cont.continuousAt.tendsto.comp (hB.prodMk_nhds (tendsto_const_nhds (x:=fun _=> X))) )
  calc
     _ = discrep F₁ F₂ (W 1) := tendsto_nhds_unique hU (hw.congr' ((ht L (H.groomed f)).and (ht V (P.groomed f)) |>.mono fun i ⟨h₁,h₂⟩=>by change fish q (inFine L i ∘ g) - fish q (inFine V i ∘ g) = Tensor.diagonal (spray L.inFT q i) X -Tensor.diagonal (spray V.inFT q i) X; rw [h₁,h₂,add_sub_add_right_eq_sub]))
     _ = _ := congr_arg (discrep F₁ F₂) ((congr_fun iteratedDeriv_one 0).trans (L.faster X).deriv)

variable {b : Matrix (Body 1 f) (Body 1 c) ℝ}
include L H hq
lemma cleaning (X : ChartVars F G) (v : Dir G c) (hx : Tendsto (fun i=> (v, relative F (Y i) v)) atTop (𝓝 X)) (ht : Tendsto Y atTop (𝓝 b))
    (hp : Junction (inFine L) (inFine V) (q-1)) : discrep (H.planeTensor f q) (P.planeTensor f q) (stretch F X)=discrep (H.planeTensor f q) (P.planeTensor f q) (polish b v) := by
   have hd : Continuous (discrep (H.planeTensor f q) (P.planeTensor f q)) := by let d := fun y:Dir G f=> fun _i:Fin q=>y; exact ((H.planeTensor f q).cont.comp (continuous_pi (A:=fun (_i:Fin q)=>Dir G f) fun _=>continuous_id)).sub ((P.planeTensor f q).cont.comp (continuous_pi fun _=>continuous_id))
   have hs : Continuous (stretch (G:=G) (S:=S) F) := by
      have ht (x) : stretch (G:=G) F x = (fderiv ℝ (Work.F03.inclusion F (G:=G)) 0 x).2 := (congr_arg Prod.snd (inclusion_deriv F _)).symm
      rw [funext ht]; fun_prop
   apply tendsto_nhds_unique ((hd.comp hs |>.tendsto _).comp hx)
   refine ((hd.tendsto _).comp (polish_tends v ht)).congr (fun i=> ?_)
   obtain ⟨z,hz⟩:=relativeGauge F (Y i) v
   change _ = discrep _ _ (stretch F (v,relative F (Y i) v)); rw [hz]; exact gauge_null H P q _ hq z hp
end transfer

-- Output differences now pushed to installed limiting shape once, at one fixed period.
omit V in
lemma realized_jet_match (v : Dir G c) (q) (hq : q≤4) : ∀ᶠ i in atTop,
     tag q (inFT L i ∘ paired v (fun t : ℝ=>ρ i (t • v))) = tag q (fun s:ℝ=>inBase L i (s • v)) := L.classic.mono fun i hi=> by
  obtain ⟨hg,h,hx⟩ := hi q hq t
  exact (ray_tag _ (hg.of_le (m:=q) le_top) v).trans (by rw [hx]; exact Eq.symm (ray_tag _ (h.of_le (m:=q) le_top) v))

section finalx
variable {W₁ W₂ Z₁ Z₂ : Shadow G} {s₁ s₂ A₁ A₂ c₁ c₂ t₁ t₂ C₁ C₂ B₁ B₂ e₁ e₂ : ℝ} (H : Passing U W₁ s₁ A₁ c₁ p) (P : Passing U' W₂ s₂ A₂ c₂ p)
    (hx : Passing R Z₁ t₁ C₁ B₁ r) (hy : Passing R' Z₂ t₂ C₂ B₂ r)
include L V H P hx hy
set_option maxHeartbeats 300000 in
lemma one_floor {q : ℕ} (hk : q=3∨q=4) (hp : Junction (inFine L) (inFine V) (q-1)) (ha : 0<η) (hb : 0<η')
    {K} (hY : Tendsto Y atTop (𝓝 K)) (v : Dir G c) :
    discrep (hx.planeTensor c q) (hy.planeTensor c q) v = discrep (H.planeTensor f q) (P.planeTensor f q) (polish K v) := by
  obtain ⟨X,hX,Qt⟩ := (critical_transfer (L.solves_slab v) (V.solves_slab v) hk (Slab.track L hp (H.groomed f) (P.groomed f)) (L.vertical_gap ha) ha (V.vertical_gap hb) hb)
  obtain ⟨A,hA,-⟩ := (L.track (L':=L) (H.everyMain f q) (H.groomed f) (H.groomed f)) q le_rfl
  obtain ⟨B,hB,-⟩ := (V.track (L':=V) (P.everyMain f q) (P.groomed f) (P.groomed f)) q le_rfl
  have hval := ((view_cont.continuousAt.tendsto.comp ((hx.mainLimit c q).1.prodMk_nhds (tendsto_const_nhds (x:=fun _ : Fin q=>v)))).sub (view_cont.continuousAt.tendsto.comp ((hy.mainLimit c q).1.prodMk_nhds (tendsto_const_nhds (x:=fun _ : Fin q=>v)))))
  calc
    _ = discrep A B (X 1) := tendsto_nhds_unique (show Tendsto (fun i:ℕ=> discrep (spray (inBase L) q i) (spray (inBase V) q i) v) atTop (𝓝 _) from hval) ((Qt hA hB).congr' ?_)
    _ = discrep _ _ (stretch F (X 1)) := unstationed L V H P (by omega : 1≤q) (X 1) hp hA hB
    _ = _ := cleaning L V H P (by omega) (X 1) v (L.pairedX v ((hX 1 (by omega)).1)) hY hp
  filter_upwards [L.realized_jet_match v q (by omega), V.realized_jet_match v q (by omega), hx.groomed c,hy.groomed c] with i h h' hf hg
  change tag q _-tag q _=Tensor.diagonal (spray (inBase L) q i) v - Tensor.diagonal (spray (inBase V) q i) v; exact congr_arg₂ (·-·) (h.trans (ray_tag _ (hf.of_le (finite_cap _)) v)) (h'.trans (ray_tag _ (hg.of_le (finite_cap _)) v))
end finalx
end YM.UVExt.Paths.Slab

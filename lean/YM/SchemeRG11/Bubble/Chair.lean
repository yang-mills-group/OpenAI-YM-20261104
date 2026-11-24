import YM.SchemeRG11.Bubble.Glass

/-!
A dressed monomial. From carrier `(i p)_L` amalgamated with remaining single-line monomial from
w to x, Fourier Gaussian gives `plume` with that list. The Taylor term with
`-‖p‖²` from σ differentiation is transformed by the same differentiation
of the Gaussian generating function at fixed open d -- don't trace with n.
This is the propagation rule even for that quadratic-momentum pole: trace in
generic d, where dimension itself varies as a function of e.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Function Set MeasureTheory Metric Filter Asymptotics Hot MSbar
open scoped ContDiff Topology
variable {n : ℕ}

def gear (F : ℝ→ℂ→Space n→ℂ) (B : ℝ) (x : Space n) (z : ℂ) (r : ℝ) : ℂ:= ∫ t in Ioc 0 B,F (t+r) z x
def stud (F : ℝ→ℂ→Space n→ℂ) (B : ℝ) (x : Space n) (z : ℂ) := gear (ember F) B x z 0

lemma inventor {Y : Type} [MeasurableSpace Y] {μ : Measure Y} {P : Y→ℝ→ℂ} {D : Y→ℂ} {b : Y→ℝ} {R C : ℝ} (hr : 0≤R) (hp : ∀ r∈Icc 0 R, Integrable (fun y=>P y r) μ) (hR : 1≤R) (hd : Integrable D μ)
    (hb : Integrable b μ) (hC : (∫ y,b y ∂μ) ≤ C) (h : ∀ᵐ y ∂μ, Ticket (P y) (D y) R (b y)) :
    Ticket (fun r=>∫ y,P y r ∂μ) (∫ y,D y ∂μ) R C := by
  refine ⟨fun t ht=> (norm_integral_le_of_norm_le hb (h.mono fun y hy=>hy.body _ ht)).trans hC,(norm_integral_le_of_norm_le hb (h.mono fun y hy=>hy.star)).trans hC, fun r hx=> ?_, fun r hx=>?_⟩
  · have he:=norm_integral_le_of_norm_le (f:=fun y=> P y r - P y 0) (hb.mul_const r) (h.mono fun y hy=>hy.ray r hx)
    rw [integral_sub (hp _ (Icc_subset_Icc_right hR hx)) (hp _ ⟨le_rfl,hr⟩),integral_mul_const] at he
    exact he.trans (mul_le_mul_of_nonneg_right hC hx.1)
  have he:=norm_integral_le_of_norm_le (f:=fun y=> P y r - (P y 0 + r*D y)) (hb.mul_const (r^2)) (h.mono fun y hy=>hy.curve r hx)
  have hi : Integrable (fun y=> P y 0 + r * D y) μ := (hp _ ⟨le_rfl,hr⟩).add (hd.const_mul _)
  rw [integral_sub (hp _ (Icc_subset_Icc_right hR hx)) hi,integral_add (hp _ ⟨le_rfl,hr⟩) (hd.const_mul _),integral_const_mul,integral_mul_const] at he
  exact he.trans (mul_le_mul_of_nonneg_right hC (sq_nonneg _))

variable {F : ℝ→ℂ→Space n→ℂ} (hf : Hearth F) {B : ℝ} {z : ℂ} {x : Space n} (hx : x≠0)
local notation "L" => (Ioc 0 B)

include hf in
lemma shuttle (r e) (x : Space n) (hr : 0≤r) : AEStronglyMeasurable (fun t=>F (t+r) e x) (volume.restrict (Ioc 0 B)) := by
  refine ContinuousOn.aestronglyMeasurable (fun t ht=> ?_) measurableSet_Ioc
  exact (hf.spark (t:=fun y:ℝ=>y+r) (continuousAt_id.add continuousAt_const) continuousAt_const continuousAt_const (add_pos_of_pos_of_nonneg (show 0<t from ht.1) hr)).continuousWithinAt

include hf hx
lemma starve (e) (R : ℝ) : ∃ C>0, ∀ r∈Icc 0 R, ∀ t∈L, ‖F (t+r) e x‖ ≤ C := by
  obtain ⟨C,hC,h⟩:= hf.globule isCompact_singleton (show 0 ∉ ({x}:Set (Space n)) from fun H=> hx ((mem_singleton_iff.mp H).symm)) (isCompact_singleton (x:=e)) (B+R)
  exact ⟨C,hC,fun r hr t ht=> h _ rfl _ rfl _ ⟨add_pos_of_pos_of_nonneg ht.1 hr.1,add_le_add ht.2 hr.2⟩⟩
lemma stream (e) (r) (hr : 0≤r) : IntegrableOn (fun t=> F (t+r) e x) L := by
  obtain ⟨C,hC,h⟩:=starve (B:=B) hf hx e r
  exact (integrableOn_const (by simp) (C:=C)).mono' (shuttle hf r e x hr) (ae_restrict_of_forall_mem measurableSet_Ioc (h r ⟨hr,le_rfl⟩))
lemma pulse (r) (hr : 0≤r) : Differentiable ℂ (fun e=> gear F B x e r) := by
  intro e
  obtain ⟨C,hC,h⟩:= hf.globule isCompact_singleton (show 0 ∉ ({x}: Set (Space n)) from fun H=> hx ((mem_singleton_iff.mp H).symm)) (isCompact_closedBall e 1) (B+r)
  refine diffuse (F:=fun e t=> F (t+r) e x) (closedBall_mem_nhds e zero_lt_one) (Eventually.of_forall fun e=> shuttle hf r e x hr) ?_ (integrableOn_const (by simp) (C:=C))
  refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t (ht : t∈L) y hy=> ?_)
  have hu:=add_pos_of_pos_of_nonneg (show 0<t from ht.1) hr
  exact ⟨hf.holds hu x y,h y hy _ rfl (t+r) ⟨hu,add_le_add_left ht.2 _⟩⟩

omit hx in
private lemma burn (c t) (hc : 0<c) (hr : 0≤t) : HasDerivAt (fun t : ℝ=> F (c+t) z x) (ember F (c+t) z x) t := by
  exact (hf.slope (add_pos_of_pos_of_nonneg hc hr) z x).comp_const_add c t

lemma fires (C : ℝ) : Glaze (gear F C x) (stud F C x) := by
  refine ⟨fun e y (hy : 0≤y)=>?_,fun r hr=> pulse hf hx r hr,pulse hf.coals hx 0 le_rfl, fun R hr K hk=>?_⟩
  · obtain ⟨b,hb,h⟩:=starve (B:=C) hf hx e (y+1)
    refine tendsto_integral_filter_of_dominated_convergence (μ:=volume.restrict (Ioc 0 C)) (l:=𝓝[Ici 0] y) (F:=fun r t=> F (t+r) e x) (fun _=>b)
      ((show ∀ᶠ v in 𝓝[Ici 0] y, 0≤v from self_mem_nhdsWithin).mono fun v hv=> shuttle hf v e x hv) ?_ (integrableOn_const (by simp)) (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht=>?_))
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by linarith : y<y+1))] with r hr hR
      exact ae_restrict_of_forall_mem measurableSet_Ioc (h r ⟨hr,le_of_lt hR⟩)
    exact (hf.spark (t:=fun u : ℝ=> t+u) (continuousAt_const.add continuousAt_id) continuousAt_const continuousAt_const (add_pos_of_pos_of_nonneg (show 0<t from ht.1) hy)).continuousWithinAt
  have hx' : 0 ∉ ({x}:Set (Space n)):= fun H=> hx ((mem_singleton_iff.mp H).symm)
  obtain ⟨A,hA,h₁⟩:=hf.globule isCompact_singleton hx' hk (C+R)
  obtain ⟨B,hB,h₂⟩:=hf.coals.globule isCompact_singleton hx' hk (C+R)
  obtain ⟨D,hD,h₃⟩:=hf.coals.coals.globule isCompact_singleton hx' hk (C+R)
  let M := A+B+D
  refine ⟨1+M*volume.real (Ioc 0 C),by unfold M; positivity,fun e he=>?_⟩
  have hp c (hc : c∈Ioc 0 C) : Ticket (fun t=> F (c+t) e x) (ember F (c+0) e x) R M := by
      have hf' t (ht : t∈Icc 0 R) : c+t∈ Ioc 0 (C+R) := ⟨add_pos_of_pos_of_nonneg hc.1 ht.1,add_le_add hc.2 ht.2⟩
      refine window (G:=fun t=> ember F (c+t) e x) (H:=fun t=> ember (ember F) (c+t) e x) hr (by unfold M; positivity) (fun t ht=> (h₁ e he x rfl _ (hf' _ ht)).trans (by unfold M; linarith))
        (fun t ht=> ⟨burn hf c t hc.1 ht.1,(h₂ e he x rfl _ (hf' _ (Icc_subset_Icc_right hr ht))).trans (by unfold M; linarith)⟩) (fun t ht=> ⟨burn hf.coals c t hc.1 ht.1,(h₃ e he x rfl _ (hf' _ (Icc_subset_Icc_right hr ht))).trans (by unfold M; linarith)⟩)
  refine inventor (μ:= volume.restrict (Ioc 0 C)) (b:=fun _=> M) (P:=fun c t=> F (c+t) e x) (by linarith) (fun t ht=> stream hf hx e t ht.1) hr (stream hf.coals hx e 0 le_rfl) (integrableOn_const (by simp)) ?_ (ae_restrict_of_forall_mem measurableSet_Ioc hp)
  rw [setIntegral_const,smul_eq_mul]; linarith

open Hearth
omit hx
lemma few {K : Set (Space n)} (hk : IsCompact K) (hT : 0 ∉ K) : ∃ Q>0, ∀ x∈K, ∀ B : ℝ, ∀ R≥1,
    Ticket (gear F B x 0) (stud F B x 0) R Q := by
  obtain ⟨A,hA,h₁⟩:=hf.medal hk hT
  obtain ⟨B,hB,h₂⟩:=hf.coals.medal hk hT
  obtain ⟨D,hD,h₃⟩:=hf.coals.coals.medal hk hT
  let g (t : ℝ) := (A+B+D)*coat t
  let s := Ioi (0:ℝ)
  have hm (t : ℝ) : 0≤g t := by unfold g coat; positivity
  have hp : IntegrableOn g s := pay_coat.const_mul (A+B+D)
  refine ⟨|∫ t in s,g t|+1,by positivity,fun x hx C R hr=>?_⟩
  have hv : x≠0:=fun H=>hT (H ▸ hx)
  refine inventor (μ:= volume.restrict (Ioc 0 C)) (b:=g) (P:=fun c t=> F (c+t) 0 x) (by linarith) (fun t ht=> stream hf hv 0 t ht.1) hr (stream hf.coals hv 0 0 le_rfl) (hp.mono_set Ioc_subset_Ioi_self) ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun c hc=>?_)
  · exact (setIntegral_mono_set hp (ae_of_all _ hm) Ioc_subset_Ioi_self.eventuallyLE).trans ((le_abs_self _).trans (by linarith))
  have h : 0<c:=hc.1
  refine window (G:=fun t=> ember F (c+t) 0 x) (H:=fun t=> ember (ember F) (c+t) 0 x) hr (hm c) ?_ (fun t ht=>⟨burn hf c t h ht.1,?_⟩) (fun t ht=> ⟨burn hf.coals c t h ht.1,?_⟩)
  · intro t ht
    exact (h₁ x hx _ (add_pos_of_pos_of_nonneg h ht.1)).trans (mul_le_mul (by linarith : A≤A+B+D) (coat_le h (by simpa using ht.1)) (sq_nonneg _) (by positivity))
  · exact (h₂ x hx _ (add_pos_of_pos_of_nonneg h ht.1)).trans (mul_le_mul (by linarith : B≤A+B+D) (coat_le h (by simpa using ht.1)) (sq_nonneg _) (by positivity))
  exact (h₃ x hx _ (add_pos_of_pos_of_nonneg h ht.1)).trans (mul_le_mul (by linarith : D≤A+B+D) (coat_le h (by simpa using ht.1)) (sq_nonneg _) (by positivity))
include hx
lemma score (B : ℝ) {r : ℝ} (hr : 0≤r) : ContinuousAt (fun x=> gear F B x 0 r) x := by
  obtain ⟨K,hK,he,h⟩:= exists_compact_subset isOpen_compl_singleton (show x∈({0}ᶜ:Set _) from hx)
  obtain ⟨C,hC,h₁⟩:=hf.medal hK (fun hu=> h hu rfl)
  have Ev : ∀ᶠ y in 𝓝 x,y∈K:=mem_interior_iff_mem_nhds.mp he
  exact tendsto_integral_filter_of_dominated_convergence (μ:=volume.restrict (Ioc 0 B)) (l:=𝓝 x) (F:=fun y t=>F (t+r) 0 y) (fun t=> C*coat t) (Eventually.of_forall fun y=> shuttle hf _ _ _ hr) (Ev.mono fun y hy=> ae_restrict_of_forall_mem measurableSet_Ioc fun t ht=> (h₁ y hy _ (add_pos_of_pos_of_nonneg (show 0<t from ht.1) hr)).trans (mul_le_mul_of_nonneg_left (coat_le ht.1 (by simpa using hr)) hC.le)) (IntegrableOn.mono_set (pay_coat.const_mul C) Ioc_subset_Ioi_self)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht=> hf.spark continuousAt_const continuousAt_const continuousAt_id (add_pos_of_pos_of_nonneg (show 0<t from ht.1) hr))

end YM.SchemeRG11.Bubble

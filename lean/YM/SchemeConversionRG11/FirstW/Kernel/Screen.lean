import YM.SchemeConversionRG11.FirstW.Kernel.Score
/-! Ordinary bump profile sampling, all fixed differences with arbitrary bounded offset. Actual position difference operators (not replacing by their leading coefficients prematurely at CT). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Metric Lattice Pert Align Topology
open scoped BigOperators ContDiff Topology
variable {T : Itinerary}
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
def nudgeR (h : ℝ) (i : Axis) (f : E4 → E) := fun x => h⁻¹ • (f (x+h • basis i)-f x)
def lens (h : ℝ) : List Axis → (E4→E) → E4 → E
 | [],f => f
 | i::D,f=> nudgeR h i (lens h D f)
-- universal (need polymorphic calculus)
def costR : List Axis → ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], (E4→E) → E4→E
 | [], _,_,_,f=> f
 | i::D,_,_,_,f=> fun v=> (costR D (fderiv ℝ f) v) (basis i)
lemma lens_has (f : E4→E) (h : ℝ) (hf : Differentiable ℝ f) (D : List Axis) (u : E4) : HasFDerivAt (lens h D f) (lens h D (fderiv ℝ f) u) u := by
  induction D generalizing u with
  | nil=> exact (hf u).hasFDerivAt
  | cons i A ih=>
    let v:=h • basis i
    have H := (((ih (u+v)).comp u ((hasFDerivAt_id _).add_const v)).sub (ih u)).const_smul (c:=h⁻¹)
    convert! H using 1
variable {h : ℕ→ℝ} {z : ℕ→E4} {v : E4}
lemma rolling (D : List Axis) : ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E4→E), ContDiff ℝ ∞ f → ∀ {h : ℕ→ℝ} {z : ℕ→E4} {v : E4}, (∀ j,0<h j) → Tendsto h atTop (𝓝 0) → Tendsto z atTop (𝓝 v) → Tendsto (fun i=> lens (h i) D f (z i)) atTop (𝓝 (costR D f v)) := by
  induction D with
  | nil=> intro E _ _ f hf h z v _ _ he; exact hf.continuous.continuousAt.tendsto.comp he
  | cons i D ih=>
   intro E instE _ f hf h z v hp hz he
   let B := costR D (fderiv ℝ f) v
   let α:=basis i
   let g (j : ℕ) := lens (h j) D f
   let e (j : ℕ) := lens (h j) D (fderiv ℝ f)
   let x (j : ℕ) := z j+h j • α
   let r (j : ℕ) := closedBall (z j) (h j)
   have ha : ‖α‖=1 := by simp [α,basis]
   have H j (u : E4) : HasFDerivAt (g j) (e j u) u := lens_has _ _ (hf.differentiable (by simp)) _ _
   have ctx {σ : ℕ→ℕ} (hs : Tendsto σ atTop atTop) {w : ℕ→E4} (hw : ∀ k,w k∈ r (σ k)) : Tendsto w atTop (𝓝 v) := by
     rw [tendsto_iff_dist_tendsto_zero]
     exact squeeze_zero (fun j=>dist_nonneg) (fun j=>le_trans (dist_triangle (w j) (z (σ j)) v) (add_le_add_left (mem_closedBall.mp (hw j)) _)) (by simpa only [comp_def,add_zero] using (hz.comp hs).add (tendsto_iff_dist_tendsto_zero.1 (he.comp hs)))
   have H0 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
   rw [Metric.tendsto_atTop]
   intro ε hε
   have hm : ∀ᶠ j in atTop, ∀ w∈r j, ‖e j w-B‖ ≤ ε/2 := by
     by_contra! hh
     have he : ∀ l:ℕ,∃ j≥l,∃ w∈r j, ε/2<‖e j w-B‖ := frequently_atTop.1 hh
     choose j hj w hw hw' using he
     have hpσ : Tendsto j atTop atTop := tendsto_atTop_mono (f:=id) hj tendsto_id
     obtain ⟨l,hl⟩ := ((tendsto_iff_dist_tendsto_zero.mp (ih (fderiv ℝ f) H0 (h:=h∘j) (fun l=>hp _) (hz.comp hpσ) (ctx hpσ hw))).eventually (gt_mem_nhds (by linarith : ε/2>0))).exists
     exact not_le.mpr (hw' l) (by rw [←dist_eq_norm]; exact hl.le)
   refine eventually_atTop.mp (hm.mono fun j hj=>?_)
   have hA (y : E4) : HasFDerivAt (fun y:E4 => g j y-B y) (e j y-B) y := (H j y).sub (B.hasFDerivAt)
   have hxj : ‖x j-z j‖=h j := by simp [x,norm_smul,ha,Real.norm_of_nonneg (hp j).le]
   have hl := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=fun y:E4=>g j y-B y) (s:=r j) (fun y _ => (hA y).differentiableAt) (C:=ε/2) (fun y hy=> (hA y).fderiv.symm ▸ hj y hy) (convex_closedBall ..) (x:=z j) (y:=x j) (mem_closedBall_self (hp _ |>.le)) (mem_closedBall_iff_norm.mpr hxj.le)
   rw [hxj] at hl
   change dist ((h j)⁻¹ • (g j (x j)-g j (z j))) (B α) < ε
   have eq : (h j)⁻¹ • (g j (x j)-g j (z j))-B α = (h j)⁻¹ • ((g j (x j)-B (x j))-(g j (z j)-B (z j))) := by simp only [x,map_add,map_smul, smul_add,smul_sub,inv_smul_smul₀ (hp j).ne']; abel
   rw [dist_eq_norm,eq,norm_smul, Real.norm_of_nonneg (inv_nonneg_of_nonneg (hp j).le), inv_mul_eq_div, div_lt_iff₀ (hp j)]
   exact hl.trans_lt (by nlinarith [hp j])
section torus
-- rounding center shift in units h
def slide (T : Itinerary) (v : E4) (F : E4→E) : Board T E := fun i x=> F (out T i x + T.gap i • v)
lemma slide_diff (s : E4) (F : E4→E) (o : ∀ i, Site (T.period i)) (hu : sails T o v) (D : List Axis) : ∀ᶠ i in atTop,
    surface D (slide T s F) i (o i) = lens (T.gap i) D F (out T i (o i)+ T.gap i • s) := by
  induction D generalizing o with
  | nil=> rw [surface_root];exact Eventually.of_forall fun _ => rfl
  | cons j D ih=>
    let b (i : ℕ):=o i+wrap (T.period i) (step j)
    have hb := sails_next hu (step j)
    have he : ∀ᶠ i in atTop, lift (b i)=lift (o i)+step j := by
      have eq (i : ℕ) : b i=wrap (T.period i) (lift (o i)+step j) := by unfold b; simp
      simp_rw [eq]; apply seals (T:=T); simp_rw [inc_add]; simpa only [out,add_zero] using (Tendsto.add hu (inc_const T (step j)))
    filter_upwards [he,ih o hu,ih _ hb] with i hi h1 h2
    have hc : out T i (b i)= out T i (o i)+T.gap i • basis j := by unfold out; rw [hi,inc_add,inc_step]
    rw [show j::D = [j]++D from rfl,←surface_surface]
    change ((T.gap i)^([j].length))⁻¹ • (surface D (slide T s F) i (o i+step j)-surface D (slide T s F) i (o i))=_
    rw [show o i+step j=b i from by unfold b; simp]
    change surface D (slide T s F) i (b i)= _ at h2
    rw [h2,h1,hc,List.length_singleton,pow_one,show [j]++D=j::D from rfl,lens,nudgeR]; rw [add_right_comm (out ..)]
variable {F : E4→E}
set_option maxHeartbeats 800000 in
lemma slide_scores (hF : ContDiff ℝ ∞ F) (s : E4) : Score T univ (slide T s F) (fun D x=>costR D F x) := by
  intro D σ hs v _ o ho
  let T':=Rig.path T σ hs
  have hz : Tendsto (fun i=>out T' i (o i)+T'.gap i • s) atTop (𝓝 v) := by simpa only [zero_smul,add_zero] using Tendsto.add ho (T'.cutoff.smul_const s)
  have e := rolling D _ hF T'.positive T'.cutoff hz
  have Hb := e.congr' (f₂:=fun i=> surface D (slide T' s F) i (o i)) (show _ from ((slide_diff (T:=T') s F o ho D).mono (fun _ ht=>ht.symm)))
  exact Hb
end torus
end YM.RG11.FirstW

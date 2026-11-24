import YM.RG11Scheme.Stencil.Loom
import YM.Pert.Rig.Linked

/-! Sequential chart calculus off separated sets. Varying observation point and subsequence index deliberately universal: supplies uniform compact bounds on native derivatives of external propagators. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.RG11Scheme.Hinge
open Function Set Filter MeasureTheory Maxwell Pert Full Align Mesh Next.Rank.Radian Stencil Stencil.Shot Stencil.Point Lattice
open scoped BigOperators Classical ContDiff Topology
variable {E F W:Type} [NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup W]
   [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ W]
variable {T : Itinerary} {V U : Set E4} {g h:ℕ→ Cover→E} {a b:E4→E} {k:ℕ}

/-- Smooth density jets (no prefactor weights). Restriction to open V assumed separately. -/
structure Works (T:Itinerary)(V:Set E4)(g:ℕ→ Cover → E)(a:E4→E)(k:ℕ):Prop where
   healthy : ∀ z∈V,ContDiffAt ℝ ∞ a z
   runs (σ:ℕ→ℕ)(hσ:Tendsto σ atTop atTop) (z:E4) (hz:z∈V)(p:ℕ→ Cover) (pick : Tendsto (fun i=>incVec (T.gap (σ i)) (p i)) atTop (𝓝 z)) (D:List Axis) (hd:D.length ≤ k):
       Tendsto (fun i=>((T.gap (σ i))^D.length)⁻¹ • go D (g (σ i)) (p i)) atTop (𝓝 (dV D a z))
lemma Works.cut (h:Works T V g a k){U:Set E4}(hu:U⊆ V){n}(hh:n≤k) : Works T U g a n := ⟨fun z hz=>h.healthy z (hu hz),fun σ q z hz p hp D he=> h.runs σ q z (hu hz) p hp D (he.trans hh)⟩
lemma Works.project (hW : Works T V g a k) : Works T V (fun i p=>g i p) a 0 := hW.cut Subset.rfl (Nat.zero_le k)
lemma Works.at_point (hp:Works T V g a k)(σ:ℕ→ℕ)(hσ:Tendsto σ atTop atTop){z:E4}(hz:z∈V){p:ℕ→ Cover}(hU : Tendsto (fun i=>incVec (T.gap (σ i)) (p i)) atTop (𝓝 z)):
    Tendsto (fun i=>g (σ i) (p i)) atTop (𝓝 (a z)) := by simpa only [List.length_nil,pow_zero,inv_one,one_smul,starting,dV,List.foldr_nil] using hp.runs σ hσ z hz p hU [] (by simp)
lemma Works.still (T:Itinerary)(V:Set E4)(z:E) : Works T V (fun _ _=>z) (fun _=>z) k := by
   refine ⟨fun _ _=>contDiffAt_const,?_⟩;intro σ hs x hx p hp D hd
   cases D with
   | nil=>simp [go,dV]
   | cons a D=>
     have he D (a:Axis): go (a::D) (fun _:Cover => z)=0 := by
        induction D generalizing a with
        | nil=> funext x; show z-z=_; rw [sub_self]; exact rfl
        | cons i D ih=> funext x; rw [onwards, ih i]; exact sub_self _
     have hv D (a:Axis): dV (a::D) (fun _:E4=>z)=(0:E4→ E) := by
        induction D generalizing a with
        | nil=> change grad a (fun _:E4=>z)=_;funext;simp [grad,Analysis.D]
        | cons i D IH=> change grad a (dV (i::D) _)=_;rw [IH];funext;simp [grad,Analysis.D]
     simpa only [he,hv,Pi.zero_apply,smul_zero] using! (show Tendsto (fun _:ℕ=>(0:E)) atTop (𝓝 0) from tendsto_const_nhds) -- rewrite goal
lemma together_deriv (hp:IsOpen V) (ha:∀ z∈V,ContDiffAt ℝ ∞ a z)(hb:∀ z∈V,ContDiffAt ℝ ∞ b z)(D:List Axis)(x:E4)(hx:x∈V): dV D (a+b) x=dV D a x + dV D b x := by
   induction D generalizing x with
   | nil=>exact rfl
   | cons i D IH=>
      have he : dV D (a+b)=ᶠ[𝓝 x] (dV D a+dV D b) := Filter.Eventually.mono (p:=fun z=>z∈V) (hp.mem_nhds hx) fun i hi=> IH i hi
      apply Eq.trans (Analysis.GermD (basis i) he)
      unfold Analysis.D
      rw [fderiv_add ((stroll D (ha x hx)).differentiableAt (by decide)) ((stroll D (hb x hx)).differentiableAt (by decide))]; exact rfl
lemma Works.plus (hW : Works T V g a k) (hH: Works T V h b k) (hx:IsOpen V): Works T V (fun i=>g i+h i) (a+b) k:= by
   refine ⟨fun x hh=>(hW.healthy x hh).add (hH.healthy x hh),?_⟩;intro σ hσ z hz p u D hd; simp_rw [together_deriv hx hW.healthy hH.healthy D z hz, plus_go,smul_add]; exact (hW.runs σ hσ z hz p u D hd).add (hH.runs σ hσ z hz p u D hd)
lemma intertwine (c:E→L[ℝ]F) (hp:IsOpen V) (ha:∀ z∈V,ContDiffAt ℝ ∞ a z) (D:List Axis)(x:E4)(hx:x∈V) : dV D (c ∘ a) x = c (dV D a x) := by
   induction D generalizing x with
   | nil=>exact rfl
   | cons i D IH=>
      have he : dV D (c ∘ a)=ᶠ[𝓝 x] c ∘ dV D a := Filter.Eventually.mono (p:=fun z=>z∈V) (hp.mem_nhds hx) fun y hy=> IH y hy
      apply Eq.trans (Analysis.GermD (basis i) he); unfold Analysis.D;rw [fderiv_comp _ c.differentiableAt ((stroll D (ha _ hx)).differentiableAt (by decide)), c.fderiv]; rfl
lemma Works.mapped (hp : Works T V g a k) (hV:IsOpen V) (A:E→L[ℝ]F) : Works T V (fun i x=>A (g i x)) (A ∘ a) k := by
   refine ⟨fun x hx=> A.contDiff.contDiffAt.comp x (hp.healthy _ hx),?_⟩
   intro σ hσ z hz p u D hd
   have hQ := (A.continuous.continuousAt (x:=dV D a z)).tendsto.comp (hp.runs σ hσ z hz p u D hd)
   rw [intertwine A hV hp.healthy _ z hz]; apply hQ.congr; intro i; change A (((T.gap (σ i))^_)⁻¹ • go D (g (σ i)) (p i))=_; rw [map_smul]; refine congrArg _ ?_; exact (go_map A.toLinearMap.toAddMonoidHom (g (σ i)) D (p i)).symm

lemma dtranslation (x:E4)(V:Set E4)(hV:IsOpen V)(ha:∀ z∈V,ContDiffAt ℝ ∞ a z)(D:List Axis)(z:E4)(hz:z+x∈V) : dV D (fun p=> a (p+x)) z = dV D a (z+x) := by
   induction D generalizing z with
   | nil=> rfl
   | cons i D IH =>
      have he : dV D (fun p=>a (p+x))=ᶠ[𝓝 z] (fun p=>dV D a (p+x)) := (((continuous_id (X:=E4)).add continuous_const (f:=id) (g:=fun _=>x)).continuousAt (x:=z) |>.eventually_mem (hV.mem_nhds hz)).mono (fun w hw=>IH w hw)
      apply Eq.trans (Analysis.GermD (basis i) he); unfold Analysis.D
      let μ:=fun w=>w+x
      have ha' := ((stroll D (ha _ hz)).differentiableAt (by decide)).hasFDerivAt
      have hx': HasFDerivAt (𝕜:=ℝ) μ (ContinuousLinearMap.id ℝ _) z:= (hasFDerivAt_id z).add_const _
      erw [(HasFDerivAt.comp (g:=dV D a) (f:=μ) z ha' hx').fderiv];exact rfl
lemma Works.slide (hp:Works T V g a k) (hV:IsOpen V) {p:ℕ→ Cover}{x:E4}(he:Tendsto (fun i=> incVec (T.gap i) (p i)) atTop (𝓝 x)) : Works T (V:= {z:E4|z+x∈V}) (fun i y=>g i (y+p i)) (fun z=>a (z+x)) k := by
   refine ⟨fun z hz=> ContDiffAt.comp (g:=a) (f:=fun z=>z+x) z (hp.healthy _ hz) (contDiffAt_id.add contDiffAt_const),?_⟩
   intro σ hσ z hz q hu D hd; rw [dtranslation x V hV hp.healthy _ z hz]; simp_rw [shifted]; refine hp.runs σ hσ (z+x) hz (fun i=>q i+p (σ i)) ?_ D hd
   apply Tendsto.congr _ (hu.add (he.comp hσ));intro i; simp only [inc_row,row_add,Function.comp_apply,smul_add]
lemma Works.wander (hp:Works T V g a k)(hV:IsOpen V)(x:Cover): Works T V (fun i p=>g i (p+x)) a k := by simpa only [add_zero,Set.setOf_mem_eq] using hp.slide hV (Align.inc_const T x)
end YM.RG11Scheme.Hinge

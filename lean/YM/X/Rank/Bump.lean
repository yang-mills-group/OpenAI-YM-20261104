import YM.X.Rank.Scope
/-!
# Weighted detection of an orthogonal color orbit point

Apply to any finite list of observables. Polynomial moments are known from using
extra copies at **other** Euclidean points with correlated color data after
replacing the covariance.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank.Screen
open Function Set Filter MeasureTheory Matrix Metric
open YM.Next.SectorChange.Gaussian YM.Next.Rank.Normal MvPolynomial Heat
open scoped Topology BigOperators Classical Kronecker NNReal
variable {I A:Type} [Fintype I] [DecidableEq I][Fintype A]

section extension
variable {Y Z : Tile I → PTS A} (hy:Continuous Y)(hz:Continuous Z)
variable (he : ∀ p:MvPolynomial A ℝ, Mirrors (fun x:Tile I=> ((↑(aeval (Y x) p - aeval (Z x) p):ℂ))))
include hy hz he
lemma joined (f:PTS A→ℝ)(hf:Continuous f)(g:PTS (Walls I) →ℝ)(hg:Continuous g)(hG: HasCompactSupport (g ∘ screen I)):
    (∫ x, g (screen I x)*(f (Y x)-f (Z x)) ∂cloudP (1:TileK I))=0:= by
  let G := g ∘ screen I; have ht : Continuous G:=hg.comp (snaps _)
  let K:= Y '' tsupport G ∪ Z '' tsupport G; have hK:IsCompact K:=(IsCompact.image hG hy).union (IsCompact.image hG hz)
  let μ:= cloudP (1:TileK I); let pair (f:PTS A→ℝ):Tile I→ℝ:= G*((f ∘ Y)-(f ∘ Z))
  have hv (f:PTS A→ℝ)(hf:Continuous f) : Integrable (pair f) μ:=(ht.mul ((hf.comp hy).sub (hf.comp hz))).integrable_of_hasCompactSupport hG.mul_right
  change ∫ x,pair f x ∂μ=0
  refine tamePay (hv f hf) (show Integrable (fun x=>2*|G x|) μ from ((ht.integrable_of_hasCompactSupport (μ:=μ) hG).abs.const_mul _)) fun ε hε=> ?_
  obtain ⟨p,hp⟩:= polish K f hf hK ε hε; let F (x:PTS A):= aeval x p; have h₁ : Continuous F:= by
    -- continuous eval
    exact MvPolynomial.continuous_eval ..
  refine ⟨pair F,hv F h₁,?_, ?_⟩
  · apply Complex.ofReal_injective
    obtain ⟨-,h⟩:= continuousPay (he p) (walls (I:=I)) hg (1:TileK I) Matrix.PosDef.one
    change (∫ x:Tile I,g (snapshots (walls (I:=I)) x) • ((↑(aeval (Y x) p - aeval (Z x) p):ℂ)) ∂μ)=_ at h
    have hI x:g (snapshots (walls (I:=I)) x) • ((↑(aeval (Y x) p - aeval (Z x) p):ℂ))=↑(pair F x):=by rw [Complex.real_smul]; push_cast; change _=(↑(g (snapshots _ _) * (F _ - F _)):ℂ); push_cast; rfl
    rw [funext hI, integral_complex_ofReal] at h; simpa using h
  intro x; change ‖G x * (_ - _) - G x * (_ - _)‖ ≤ _
  rw [← mul_sub,norm_mul]; by_cases hx:G x=0
  · simp [hx]
  have h₀:x∈tsupport G:= subset_closure hx
  have hy':= hp _ (Or.inl ⟨x,h₀,rfl⟩); have hz':=hp _ (Or.inr ⟨x,h₀,rfl⟩)
  refine le_trans (b:= ‖G x‖*(ε+ε)) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) ?_
  · change ‖(f (Y x)-f (Z x))-(F (Y x)-F (Z x))‖ ≤ ε+ε; rw [sub_sub_sub_comm]; refine (norm_sub_le ..).trans (add_le_add ?_ ?_ )
    · rw [norm_sub_rev]; exact hy'
    rw [norm_sub_rev]; exact hz'
  simp only [Real.norm_eq_abs]; exact le_of_eq (by ring)
end extension

private lemma positive_test {f:Tile I→ℝ}(hf:Continuous f)(hF:HasCompactSupport f)(h:0≤f)(hh:f (Screen.one I) ≠ 0) : 0<∫ x,f x ∂cloudP (1:TileK I):= by
   let P:=price (1: TileK I); have hc:P.PosDef:= tall _ Matrix.PosDef.one
   rw [cover_int hc]; let F:=ratio P * f; have H : Continuous (ratio P):= by unfold ratio force dotProduct Matrix.mulVec dotProduct; fun_prop
   have hi:= (H.mul hf).integrable_of_hasCompactSupport (μ:=volume) hF.mul_left
   exact integral_pos_of_integrable_nonneg_nonzero (f:=F) (x:=Screen.one I) (H.mul hf) hi (fun x=>mul_nonneg (ratio_pos hc x).le (h x)) (mul_ne_zero (ratio_pos hc _).ne' hh)

def ledge {Z:Type*}[PseudoMetricSpace Z](y:Z)(δ:ℝ)(x:Z) := max (δ-dist x y) 0
lemma ledge_pos {Z:Type*}[PseudoMetricSpace Z] (x y:Z)(δ:ℝ): ledge y δ x≠0 → x∈ball y δ:= by unfold ledge; intro hx; by_contra ht; exact hx (max_eq_right (sub_nonpos.mpr (le_of_not_gt ht)))
lemma detects (Y Z : Tile I→PTS A)(hy:Continuous Y)(hz:Continuous Z)(hp:∀ p : MvPolynomial A ℝ,Mirrors (fun x:Tile I=> ((↑(aeval (Y x) p-aeval (Z x) p):ℂ)))) :
   ∃ x:Tile I,gram x=1 ∧ Y x= Z (Screen.one I):= by
   let u:=screen I; let i:=Screen.one I; have hi:Continuous u:= snaps _
   let A x:=(u x,Y x)
   obtain ⟨δ,hδ,hK⟩:= collar I; let K:= u ⁻¹' closedBall (u i) δ; let z:=(u i,Z i)
   by_contra! H
   have hw:z∉A '' K:=by rintro ⟨x,hx,ht⟩; exact H x (gram_facts (Prod.mk.inj ht|>.1)) (Prod.mk.inj ht|>.2)
   obtain ⟨ε,hε,H⟩:= Metric.isOpen_iff.mp ((hK.image (hi.prodMk hy)).isClosed.isOpen_compl) z hw
   let p:= min δ ε; have ht:0<p:=lt_min hδ hε; let f:=ledge (Z i) p; let g:=ledge (u i) p
   let w:=g ∘ u; have hg:Continuous g:= by unfold g ledge; fun_prop
   have hf:Continuous f:= by unfold f ledge; fun_prop
   have he: ∀ (x:Tile I), w x≠0 → dist (u x) (u i) < p := fun x hx=>ledge_pos _ _ _ hx
   have h₀(x) (hx:w x≠0) : x∈K:= (he x hx).le.trans (min_le_left δ ε) -- defin eq
   have hW:HasCompactSupport w:= (show IsCompact K from hK).of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun x hx=>h₀ x hx) hK.isClosed); let Q:=w * (f ∘ Z)
   have hQ:0<∫ x,Q x ∂cloudP (1:TileK I):= positive_test ((hg.comp hi).mul (hf.comp hz)) hW.mul_right (fun x=> mul_nonneg (le_max_right ..) (le_max_right ..)) (by change ledge _ p (u i)*ledge _ p (Z i)≠0; simp [ledge, max_eq_left ht.le, ht.ne'])
   have ht₀:= joined hy hz hp f hf g hg hW
   have hh x : g (screen I x)*(f (Y x)-f (Z x))= -Q x:= by
     suffices hh:w x*f (Y x)=0 by
       rw [mul_sub]; change w x * f _-_= - (w x * f _); rw [hh,zero_sub]; rfl
     by_contra h
     obtain ⟨ha,hg⟩:=mul_ne_zero_iff.mp h
     have h': (A x)∈ ball z p:= by rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]; exact ⟨he x ha,ledge_pos _ _ _ hg⟩
     exact H (ball_subset_ball (min_le_right ..) h') ⟨x,h₀ x ha,rfl⟩
   simp_rw [hh,integral_neg,neg_eq_zero] at ht₀; exact hQ.ne' ht₀
end YM.PositionX.Rank.Screen

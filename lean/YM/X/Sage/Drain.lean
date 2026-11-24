import YM.X.Sage.Session
/-!
# λ prices vanish if masks.Unpumped. contour budget root rank. Exact color cancellation independent of orientation. Uses Geom only for majority β and stale β.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k p q₁ q₂:ℕ} {V:Type*} {q:ℕ+} {r t R:ℝ}
local notation "L"=> (atTop:Filter ℕ)
local notation "U"=> G.ColorIndex
local notation "θ"=> Reed.Horizontal G
local notation "T"=> Tet
local notation "Q"=> qu q G k
local notation "P₁"=> μDeck q G
local notation "P₂"=> βDeck q G
variable {f g h': Foam G}{b:Curly G} (x y z:Fielding.Walk)
variable (χ:Floor R)(h:Geom q r x y z)(hr:R<r) (hq:1<q.val)
local notation "K"=> Set.univ (α:=Marks G)
local notation "Y"=> terminals G (-1)
local notation "H"=> Hair G
local notation "Iτ"=> Core q x y z (B₁:=K) (B₂:= Y) (B₃:= Y) (T₁:={3}) (T₂:={2}) (T₃:={2})
local notation "W₀" => (fades ℂ)
include h hq χ hr
lemma cull_stair (hb:p∈ ({2,3}:Set ℕ))(hm:q₁+q₂ + p=3): Iτ p q₁ q₂ W₀:= by
    intro F T' V hF hT hv; have hr':= χ.positive.trans hr; refine Tot.lack x y z Y Y _ _ _ (illA _ _ hF hq hr') hT hv (d:=3-p) (Page.duty' hF ?_) ?_ h hr' hq (same_wire h.2.1 hr'.le hq); · intro i hi; change i+p=3 at hi; omega
    intro i hi j hj; change i+q₁=2 at hi; change j+q₂=2 at hj; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb; omega
local notation "A"=> (cloak q x P₂)
local notation "Υ"=> (cloak q y P₁)
local notation "Vτ"=> (cloak q z P₁)
lemma perish : mantle q (deckQ q χ x) A Υ Vτ (EngineP q G) ∈ W₀:= by
    have he: P₂∈Page q {3} K:= home_close q _ (Set.Subset.refl _) (subset_univ _) degreeB; exact page_maj q x y z χ A Υ Vτ (launch_ _ _ _ _ _ he) (launch_ _ _ _ _ _ degreeU) (launch_ _ _ _ _ _ degreeU) _ usual_fading h hq hr (shape_health hq) (cull_stair x y z χ h hr hq (by simp) rfl) (cull_stair x y z χ h hr hq (by simp) rfl) (cull_stair x y z χ h hr hq (by simp) rfl)
lemma arrest (hx:Apt q r f)(hp:heightY f 3): gather q x y z f P₁ P₁∈ W₀:= by have hz:=χ.positive.trans hr; exact Tot.lack x y z Y Y f _ _ hx degreeU degreeU hp (by simp) h hz hq (same_wire h.2.1 hz.le hq)
omit h hq χ hr
-- exact stale-U. masked and not. Body.Scroll recommended
lemma snapβ (x:Cover): dress (G:=G) x (βDeck q G k)= cubicP (fun a=>glyph (psiF q k x 1 0 a)) (fun a=>glyph (psiF q k x 1 1 a)) (fun a=>glyph (psiF q k x 1 2 a)):= by rw [ward_deck]; unfold cubicP βm; simp_rw [Finset.sum_apply,Pi.smul_apply,Pi.mul_apply,map_sum,map_smul,map_mul,pass_f]
lemma snapμ (x:Cover): dress (G:=G) x (μDeck q G k)= ∑ i:T,∑ a:U, glyph (psiF q k x (-1) i a)*glyph (psiF q k x (-1) i a):= by rw [tune_deck]; unfold μm; simp_rw [Finset.sum_apply,Pi.mul_apply,map_sum,map_mul, pass_f]
lemma dressing (x:Cover)(hp:duty b d): duty (dress x b) d:= hp.affine _ (fun i=> (by rw [dress,rename_X]; apply duty.x))
lemma bedrock (h:heightY f 2): gather q x y z P₂ f P₁=0:= by
     ext1 k; simp_rw [Tot.gather,snapβ,snapμ,cubicP,tri_sum,tri_scale]; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro b _; apply Finset.sum_eq_zero; intro c _; by_cases hv:a≠b∧b≠c∧c≠a; · apply smul_eq_zero_of_right; simp_rw [tri_sum₂]; apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro u _; apply burden _ _ _ _ _ _ (dressing _ (h k)); all_goals simp_rw [ψ_meetPP]; (rcases hv with ⟨hx,hh,ht⟩); (by_cases h1:a=u<;>by_cases h2:b=u<;>by_cases h3:c=u)<;> grind
     rw [Sage.lack a b c hv,Complex.ofReal_zero,zero_smul]
-- stencil envy. feu. length.Body.Memory.
lemma horizonB (x:Cover)(b:Curly G)(hb:b∈tripleSpan G): dress x b∈ tripleSpan G:= by
   change b∈Submodule.comap (dress x).toLinearMap (tripleSpan G); refine Submodule.span_le.mpr ?_ hb; rintro _ ⟨i,j,k,h,g,t,rfl⟩ -- motive goal? need stating comap
   simp only [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply,dress,map_mul,rename_X]; exact generated _ _ _ h g t
lemma myth (x:Cover)(b:Curly G)(hb:b∈tripleSpan G)(v:T)(a:U):
   multi Q (glyph (psiF q k x r v a)*glyph (psiF q k x r v a)) b=0:= by
   change b∈LinearMap.ker (toned Q (glyph (psiF q k x r v a)*_)); apply Submodule.span_le.mpr _ hb; rintro _ ⟨i,j,k',hi,hj,hk,rfl⟩; change multi Q _ _=0; have he(w:Hair G):X (R:=ℂ) w=glyph (Finsupp.single w 1):=by rw [glyph,Finsupp.linearCombination_single,one_smul]
   have hh(w z:H) (ht:w.2≠ z.2): treats Q (Finsupp.single w 1) (psiF q k x r v a)=0 ∨ treats Q (Finsupp.single z 1) (psiF q k x r v a)=0:= by
       by_cases h:w.2 = a; · right; exact ψ_paint x v a z (h ▸ ht.symm)
       left; apply ψ_paint;exact h
   simp_rw [he]; exact band_left _ _ _ _ _ (hh i j hi) (hh j k' hj) (hh i k' hk.symm)
lemma steal (W: Billboard G q)(J V': Billboard G q)(h:∀ (i:ℕ)(z:Site (side q i)),W i z∈ tripleSpan G)(g:Weave q): mantle q g (cloak q x P₁) J V' W=0:= by
    ext1 k'; unfold mantle crow majority; rw [Finset.sum_eq_zero,mul_zero]; · rfl
    intro i _; simp only [Pi.mul_apply,cape_val,snapμ]; let q':=qu q G k'; change g k' i * tri q' ((toned q').flip (W k' i) (∑ s:T,∑ b:G.ColorIndex,_)) _ _=0; simp_rw [map_sum, LinearMap.flip_apply]; simp only [show ∀ a:Curly G,toned q' a (W k' i)=multi q' a (W k' i) from fun _=>rfl,q',myth (x k') _ (h k' i), Finset.sum_const_zero, tri_z, mul_zero]
lemma helm (i:ℕ)(z:Site (side q i)): EngineP q G i z ∈tripleSpan G:= by unfold EngineP; rw [viz_val]; unfold shape priceCo; rw [map_smul]; exact Submodule.smul_mem _ _ (horizonB _ _ pillar_type)
include h χ hq hr
lemma pricestop : CostF (priceF q χ x y z P₂ P₁ P₁ (EngineP q G)) (Tot.relevant q A Υ Vτ (EngineP q G)) := by
   unfold priceF bill; rw [steal y (EngineP q G) _ _ helm _,steal z (EngineP q G) _ _ helm _,add_zero,add_zero]; unfold CostF; rw [add_sub_cancel_left];exact perish x y z χ h hr hq
end YM.PositionX.Sage

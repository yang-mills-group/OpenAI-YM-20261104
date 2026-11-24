import YM.X.Sage.Sermon
/-!
# Ω price replacement. Exact topology cancellation, ε cost only from stencil. important cost uses distinct.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V:Type*} {n:Side}{q:ℕ+} {r R:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "U"=> G.ColorIndex
local notation "θ"=> Reed.Horizontal G
local notation "Θ"=> (⊤:Submodule ℝ (Fan G))
local notation "T"=> Tet
local notation "P"=> Curly G
local notation "o"=> side q k
local notation "Q"=> flow G n
variable (a b c:Curly G) -- explicit variable bug use full!
lemma school_d (x y:Cover)(p:Curly G)(h:wrap n x= wrap n y): school Q a b c (dress x p)=school Q a b c (dress y p):= by
   unfold school; simp_rw [contributor (n:=n) (0:Site n) a b c,pay_sym (n:=n) (0:Site n) _ _ _, tint, h] -- pay_sym rewrites both sides loops? Pay_sym rewrite itself expands Sale etc.
variable (x y z:Fielding.Walk)(A B C:Foam G)(χ:Floor R)
abbrev levy (q:ℕ+)(x y z:Fielding.Walk)(A B C V:Foam G): ℕ→ℂ := Tot.relevant q (cloak q x A) (cloak q y B) (cloak q z C) (vertexLift q V)
local notation "F"=> levy q x y z A B C
lemma levy_plus (a b:Foam G): F (a+b)= F a+F b:= by unfold levy; rw [map_add,relevant_v]
lemma levy_sub (a b:Foam G): F (a-b)=F a-F b:= by rw [← add_sub_cancel_right (F (a-b)) (F b), ← levy_plus, sub_add_cancel]
lemma levy_scaled (u:ℕ→ℂ)(a:Foam G): F (u • a)=u*F a:= by unfold levy; rw [viz_p,rv_scale]
lemma escort (a:Curly G)(t:Cover)(i:ℤ): F (priceCo q i (dress t a)) = F (priceCo q i a):= by
     ext1 k'; unfold levy Tot.relevant crow; simp_rw [cape_val,viz_val]; apply congr_arg; let f(z:Cover):= dress z (priceCo q i a k'); have hh(z:Cover): dress z (priceCo q i (dress t a) k')= f (z+t):= by unfold f priceCo; rw [map_smul,map_smul,dress_addT];
     simp_rw [hh]; let n':=side q k'; let u:=wrap n' t; conv_rhs=> rw [← Equiv.sum_comp (Equiv.addRight u)]
     refine Finset.sum_congr rfl (fun i _=>?_); apply school_d; rw [map_add,wrap_lift,wrap_lift]; rfl
lemma crew_back (f:Curly G)(w:Axis): F (centerF q 4 (jumpV w f))=0 := by
    rw [jumpV,map_sub,levy_sub]; unfold centerF; change _- _= _; rw [show F (priceL q (-(↑(4:ℕ):ℤ)) (dress _ _))= F (priceL q (-(↑(4:ℕ):ℤ)) f) from escort x y z A B C f (step w) (-(↑(4:ℕ):ℤ)),sub_self]
lemma wake_down : F (centerF q 4 (wake G))=0:= by unfold wake; simp_rw [map_sub,map_add,map_sub,levy_sub,levy_plus,levy_sub,ttop,crew_back]; ring
abbrev tollV₁ (q:ℕ+)(G:Gauge):Foam G:= centerF q 4 (minus_vertex G)
def highA (q:ℕ+)(a:G.ColorIndex):Foam G:= ∑ p:T, μm q p a*bcomp q (-1) p a
lemma vista : tollV₁ q G=∑ a:U, highA q a:= by unfold tollV₁ highA minus_vertex;simp_rw [map_sum, center_mul (d:=2) (m:=2),center_x];rfl
lemma ash_verse₃ (q:ℕ+){p:Curly G}(h:p∈verse Θ 5)(he:HC p 3) (hq:1<q.val): zoomA q (-1) (centerF q 4 p)∈ myPage q G:= by
   change zoomA q _ (priceCo q (-(↑(4:ℕ):ℤ)) (p))∈ _; rw [price_zoom]; let b:= priceCo q (-(↑(5:ℕ):ℤ)) p; change priceCo q (-(↑(5:ℕ):ℤ)) p∈ _; rw [← price_cut (n:=(-(↑(5:ℕ):ℤ))) (q:=q) he]; -- not let pattern
   exact through q (Set.univ (α:=Tops G)) (verse_page q hq h) -- arg
lemma cubic_hc (f g h:U→P)(hf: ∀ i,HC (f i) 1)(hg:∀i,HC (g i) 1)(hp:∀i,HC (h i) 1): HC (cubicP f g h) 3:= by unfold cubicP; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; apply IsWeightedHomogeneous.sum; intro k _; rw [← C_mul']; exact ((hf i).mul ((hg _).mul (hp _))).C_mul _
lemma junk (i j k l:Axis): HC (ttop (G:=G) i j k l) 3:= by refine hcsub (dress_hc ?_ _) (?_); all_goals apply cubic_hc <;> (intro _; exact isWeightedHomogeneous_X ..)
lemma wake_three : HC (wake G) 3:= hcsub (IsWeightedHomogeneous.add (hcsub (junk ..) (junk ..)) (junk ..)) (junk ..)
lemma minus_three : HC (minus_vertex G) 3:= by
    unfold minus_vertex; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; rw [reciter,Emitter,map_sum]; simp_rw [map_smul, call_X]; refine (HCglyph _).mul (n:=2) ?_; apply IsWeightedHomogeneous.sum; intro v _; rw [←C_mul']; apply IsWeightedHomogeneous.C_mul; unfold glove; apply IsWeightedHomogeneous.sum; intro u _; apply IsWeightedHomogeneous.sum; intro x _; rw [←C_mul']; exact (hcmul (isWeightedHomogeneous_X ..) (isWeightedHomogeneous_X ..)).C_mul _
variable (h:Geom q r x y z)(hr:R<r)(hq:1<q.val)
local notation "K"=> (fades ℂ)
include h hr hq χ
lemma levy_down (hA:A∈Ready q θ)(hB:B∈Ready q θ)(hC:C∈Ready q θ): CostF (F (shape q)) (F (tollV₁ q G)):= by
    unfold CostF; let p:Curly G:= Tot.pillar G-(minus_vertex G+wake G); let H:=centerF (G:=G) q 4; rw [← levy_sub,show shape q-tollV₁ q G= H p+centerF q 4 (wake G) from ?_, levy_plus, wake_down,add_zero]; swap; · unfold p; change H (Tot.pillar G) -H _=_; rw [map_sub,map_add]; unfold H; abel
    nth_rw 1 [← zoom_back (H p)]; rw [zoom_pose,levy_scaled]; refine epi_d q hq _ ?_; apply (page_full q x y z χ _ _ _ (launch_ _ _ _ _ _ hA) (launch_ _ _ _ _ _ hB) (launch_ _ _ _ _ _ hC) crew usual_crew h hq hr (ash_verse₃ q tollV (hcsub roarP (IsWeightedHomogeneous.add minus_three wake_three)) hq) (inner_crew q x y z h hq (χ.positive.trans hr))) -- apply equival
local notation "rN"=> levy q x y z (βDeck q G) (μDeck q G) (μDeck q G)
lemma levy_n : CostF (priceF q χ x y z (βDeck q G) (μDeck q G) (μDeck q G) (EngineP q G)) (rN (tollV₁ q G)) := (pricestop x y z χ h hr hq).trans (levy_down x y z _ _ _ χ h hr hq (single_ready degreeB) (single_ready degreeU) (single_ready degreeU))
end YM.PositionX.Sage

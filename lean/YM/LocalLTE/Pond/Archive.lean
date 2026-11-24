import YM.LocalLTE.Pond.Digest
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes Urns
variable {G} {P:BudgetPoint} {o:Site n} {R:PathData G} {κ k α Δ σ C' Λ η :ℝ} {c:Clip}
variable (hn: 3 ≤ P.B) (hP:WilsonStartup.Decent c P) (hR: R.Bounds c σ C' Λ) (hS: Reliable G κ k)
open Grove
open Urns
def Comic (G:Gauge) (X: RegularAddress n)(Z:BudgetPoint)(f:Config G n→ℝ): Prop:= Z.Regular X.support f ∧ f 1=0 ∧ ∀ (_: Nonwrapping X.support X.site)(v w: Directions G n), IsAffineDirection X.site v→ IsAffineDirection X.site w → logHessian f v w=0
lemma movie {i:ℕ}{X:Grove o} (ht:Reliable G κ k)(f:Config G n→ℝ)(h:P.Regular (neighbors i o) f) (hF:ContDiffAt ℝ (pie j+1) (f ∘ soloV) 0) :
    Comic G ⟨o,neighbors i o,(neighbors_mem ..).2 (by simp)⟩ P f → Comic G ⟨o,neighbors i o,(neighbors_mem ..).2 (by simp)⟩ P (shave X i κ (pie j+1) f):=by
     rintro ⟨_,hh,hP⟩; let g:= shave X i κ (pie j+1) f; have he :∃ h₂: g 1=f 1, True:= by
       have ht:= Hall.roots i X ht (pie j+1) P f h hF 0 (by unfold pie; omega); refine ⟨?_,trivial⟩
       change iteratedFDeriv ℝ 0 (g∘increment 1) _=_ at ht; simpa only [iteratedFDeriv_zero_apply,Function.comp_apply,Work.G07.at_zero_increment] using DFunLike.congr_fun ht (fun _:Fin 0=>(0:Directions G n))
     exact ⟨LocalLTE.FrameBox.legal X i ht _ P,(Classical.choose he).trans hh, fun hp v w hv hw=> (DFunLike.congr_fun (Hall.roots i X ht (pie j+1) P f h hF 2 (by unfold pie; omega)) ![v,w]).trans (hP hp v w hv hw)⟩
lemma flick {a : RegularAddress n}(P: BudgetPoint) : Comic G a P 0:=by
    refine ⟨reg_const _,rfl,fun hp v w hv hw=>?_⟩
    unfold logHessian; change iteratedFDeriv ℝ 2 (fun _:Directions G n=>(0:ℝ)) _ _=0; rw [iteratedFDeriv_const_of_ne (by norm_num)]; rfl
-- Can't infer NONWRAPPING from smaller.Anabolic. require GIR.Scalar equality anyway
lemma staple {X:Grove o} (p: BudgetPoint) (i:ℕ) (ht:Reliable G κ k)(f:Config G n→ℝ)(h:p.Regular (neighbors i o) f) (hF:ContDiffAt ℝ (↑ (pie j+1): WithTop ℕ∞) (f ∘ soloV) 0) (Y:Support n)(he:neighbors i o ⊆ Y)(hz:o ∈ Y) (hh : f 1=0) (ha:∀ (_:Nonwrapping Y o)(v w:Directions G n),IsAffineDirection o v→IsAffineDirection o w→logHessian f v w=0) : Comic G ⟨o,Y,hz⟩ p (shave X i κ (pie j+1) f):=by
    let g:= shave X i κ (pie j+1) f; have hu: g 1=f 1:= by
       have ht:= Hall.roots i X ht (pie j+1) p f h hF 0 (by unfold pie; omega)
       change iteratedFDeriv ℝ 0 (g∘increment 1) _=_ at ht; simpa only [iteratedFDeriv_zero_apply,Function.comp_apply,Work.G07.at_zero_increment] using DFunLike.congr_fun ht (fun _:Fin 0=>(0:Directions G n))
    exact ⟨reg_larger (LocalLTE.FrameBox.legal X i ht _ _) he,hu.trans hh,fun hp v w hv hw=> (DFunLike.congr_fun (Hall.roots i X ht (pie j+1) p f h hF 2 (by unfold pie; omega)) ![v,w]).trans (ha hp v w hv hw)⟩

-- smooth at all origin. Use chart or differential for post high stroke
lemma lowAt (i:Low) (Δ:ℝ) (c:Clip) (s:ℕ) (p:BudgetPoint)(R:PathData G)(o:Site n)(h: WilsonStartup.Decent c p) : ContDiffAt ℝ (s:WithTop ℕ∞) (Low.fresh R c i o Δ ∘ soloV) 0:=by
   have he := (Low.fresh_bill R c i o h Δ); rw [← Hall.bare]; exact ((he.smooth [] (by simp) 1).of_le (by exact_mod_cast (le_top : (s:ℕ∞)≤⊤))).contDiffAt
lemma highAt (R:PathData G) (i:High)(o:Site n)(p: BudgetPoint) (α Δ: ℝ)(s:ℕ): ContDiffAt ℝ (↑s) (High.fresh R i o α Δ ∘ soloV) 0:= by
   have he:= High.fresh_bill R i o p α Δ; rw [← Hall.bare]; exact ((he.smooth [] (by simp) 1).of_le (by exact_mod_cast (le_top : (s:ℕ∞)≤⊤))).contDiffAt
include hn hP hS
lemma payL (hG:G.Simple)(o:Site n)(ht:20<n.val)(i:Low)(Δ:ℝ) : Comic G ⟨o,Low.home R i P o,Low.small_home ..⟩ P (swan R c P j κ o Δ i):=by
    unfold swan; split
    next h=>
       refine staple (X:=cane o) P (P.B-1) hS (Low.fresh R c i o Δ) (Price.lousy P c R o hn hP i Δ h) (Price.lowAt i _ _ _ P R o hP) (Low.home R i P o) ?_ _ (Low.fresh_one R c i o Δ) (fun H x y=> Low.fresh_vanish R c i o hG hP H ht Δ x y)
       exact (Corona.halo_mono (Nat.sub_le ..) (Finset.Subset.refl _)).trans (Low.halo_home R i P o)
    exact flick P
-- Art transform. including rotation by post posts.E bias. 
omit hn hP
include hR hS
lemma payH (o:Site n)(i:High)(hG:G.Simple)(α Δ:ℝ): Comic G ⟨o,bloomH R P o i, Price.erect R P o i (High.small_home ..)⟩ P (craneH R P j κ o α Δ i):=by
    unfold craneH; split
    next h=>
       refine staple (X:=cane o) P P.B hS (High.fresh R i o α Δ) (reg_larger (High.fresh_regular R i o hR P α Δ) (tightH P R o i h.le)) (Price.highAt _ _ _ P _ _ _) (bloomH R P o i) ?_ _ (High.fresh_one R i o α Δ) (fun _ v w _ _ => High.fresh_vanish R i o hG hR P α Δ v w)
       rw [bloomH,if_pos h]; exact Corona.halo_mono (by omega) (Finset.Subset.refl _)
    exact Price.flick _
omit hS hR
lemma Comic.out {x:RegularAddress n}{f :Config G n→ℝ} (h:Comic G x P f)(y:RegularAddress n)(he:y.site=x.site)(hp:x.support⊆y.support): Comic G y P f:=by
    refine ⟨reg_larger h.1 hp,h.2.1,?_⟩; rw [he]; exact fun ht=>h.2.2 (fun i hh=> ht i (hp hh))
lemma Comic.pair {x:RegularAddress n}{f g:Config G n→ℝ} (h:Comic G x P f)(he:Comic G x P g): Comic G x P (f-g):=by
    refine ⟨reg_sub h.1 he.1,(by simp [h.2.1,he.2.1]),fun ht v w ha hb=>?_⟩; rw [hessian_sub h.1 he.1, h.2.2 ht v w ha hb, he.2.2 ht v w ha hb,sub_zero]
lemma Comic.move {x:RegularAddress n}{g:Config G n→ℝ} (hG:G.Simple)(ht:20<n.val)(h:Comic G x P g)(v: Seat n)(y:RegularAddress n)(hp:y.site=affine v.1 v.2 x.site)(hv: y.support=Seat.spread v x.support): Comic G y P (g∘ v.view):=by
    have hh: P.Regular y.support (g∘v.view):=by rw [hv]; exact Seat.regular v h.1
    refine ⟨hh,by rw [Function.comp_apply,Seat.view, VerifiedReset.pull_one_field]; exact h.2.1,?_⟩
    intro ha; apply VerifiedReset.affine_zero hh y.site; intro l
    have hb:Nonwrapping x.support x.site:= by rw [hp,hv] at ha; rw [← spin_wrap v.1 v.2]; exact ha -- edit
    rw [hp]; exact (l.hessian_turn v.1 v.2 _ hb (by omega) l hG h.1).trans (h.2.2 hb _ _ ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩)) -- edit
end YM.AnalyticBridge.VerifiedReset.Collection.Price

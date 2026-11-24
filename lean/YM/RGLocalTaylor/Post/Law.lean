import YM.RGLocalTaylor.Post.Projection

/-! # Full `RegularFamily`, not merely a price at Healthy. Also buys projection after filling the actual posting. See ledger. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Post.Anchor
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens
open AnalyticBridge VerifiedReset Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat Collection Extra.Iteration Song Refrain Geo Quotes
open Residual WilsonStartup Averaging Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open UVNext.CouplingReset Input
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint}
    {X : Listing G n} {v a b : Collection.Source G n} {σ C Λ α Δ u w : ℝ}
open RGLocalTaylor.Read

variable (g : G.Simple) (h : orient p X.reg v.logRead u) (hx : R.Bounds c σ C Λ) (hc : Decent c p) (hn : 20 < n.val) (α Δ : ℝ)
include g h hx hc hn
-- VERFIED_RESET_STEP.Trays proof with only *pre-movement regular* receipt (so no fake partners).
lemma regFamily : ((shelves X R p).pours (fill X R c p v α Δ)).RegularFamily p := by
  let F := archive X R c v α Δ; let D := incoming X R p
  have hr (i : EKey n) : p.Regular (D i).support (F i) ∧ F i 1 = 0 := by
    rcases i with i|⟨z,d⟩|⟨z,d⟩
    · exact ⟨rebate_regular _ ((projection_cap h).regular i),rebate_one ..⟩
    · exact ⟨z.regular (d.fresh_regular R c 0 hc _),show d.fresh R c 0 _ (pull _ _ 1) = 0 by rw [pull_one_field,Low.fresh_one]⟩
    exact ⟨z.regular (d.fresh_regular R 0 hx p _ _), show d.fresh R 0 _ _ (pull _ _ 1) = 0 by rw [pull_one_field,High.fresh_one]⟩
  have hh (i : EKey n) (hi : Nonwrapping (D i).support (D i).site) : ∀ a b, IsAffineDirection (D i).site a → IsAffineDirection (D i).site b →
      logHessian (F i) a b = 0 := by
    rcases i with i|⟨z,d⟩|⟨z,d⟩
    · exact rebate_vanish (X.reg i) g ((projection_cap h).regular i) hi hn
    · apply affine_zero (hr _).1
      intro u; exact (z.hessian g (d.fresh_regular R c 0 hc _) hi (by omega) u u).trans (d.fresh_vanish R c 0 g hc (z.unwrapped hi) hn _ _ _
          ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩))
    apply affine_zero (hr _).1
    intro u; exact (z.hessian g (d.fresh_regular R 0 hx p _ _) hi (by omega) u u).trans (d.fresh_vanish R 0 g hx p _ _ _ _)
  exact ⟨fun i => (hr _).1,fun i => (hr _).2,fun i => hh _⟩

lemma coreRecognition (hw : Width p c σ):
    let f:=(drawer G n).pours (Rack.widen (shelves X R p) (branch X R c p v α))
    f.RegularFamily p ∧ f.EBound p (regularNeed G p c σ C α u):= by
  let Δ:= Averaging.delta (X.read v)
  let Z:= shelves X R p; let D:= Collection.branch X R c p v α
  have ht:= Rack.preserves Z D p; intro f
  refine ⟨ht.regular (regFamily g h hx hc hn α Δ),ht.Ebound ?_⟩
  obtain ⟨u',hu,hK⟩:= h
  let q:= quoteE (n:=n) R p c α Δ u'
  have h:= Averaging.delta_bound g (projection_cap (p:=p) (X:=X) (v:=v) (u:=u) ⟨u',hu,hK⟩)
  have hF := Local.quote_regular (v:=v) g hx hc α Δ (u:=u') (fun i=>(hK i).2) (fun i=>(hK i).1)
  refine ⟨q ∘ numbering _, (fun i => hF (numbering _ i)), fun x=>?_⟩
  exact Cost.equiv (numbering _) ((Local.quote_family (v:=v) hx hc hw α Δ (u:=u') (fun i=>(hK i).2) hu h).1 x)

/-- Use on ACTUAL activity catalog, attaching also its full forced family exactly as earned by `payments`. Never pointwise or repricing the denominator. -/
lemma transplant {A:Activities G n} (he:A.reg=(drawer G n).reg) (hw:Width p c σ):
    let Y:= {A with E:=central R c p X v α}
    Y.RegularFamily p ∧ Y.EBound p (regularNeed G p c σ C α u):= by
  rcases A with ⟨r,b,U,F⟩; dsimp only at he; subst r; intro Y
  obtain ⟨⟨hf,h,hv⟩, ⟨v,hX,hV⟩⟩:= coreRecognition g h hx hc hn α hw
  exact ⟨⟨hf,h,hv⟩,v,hX,hV⟩
end YM.RGLocalTaylor.Post.Anchor

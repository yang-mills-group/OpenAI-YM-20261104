import YM.IterationFour.Shore.Buffs

/-! One (not two) merger when using in the alpha continuity check.
Pre-reset species hard reserve spent at the end. -/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Shore
open Lattice Wilson RG Function MeasureTheory Filter Vacuum AnalyticBridge VerifiedReset Collection Ovens Progress.DirectedRecipe Ovens.Pipes Rack Averaging Extra.Iteration
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint}

def powder (X:Pipes G n)(d:Tap G n) : Shard G n:= ⟨X.softer,d.logarithm,X.sites⟩
def wood (X:Pipes G n)(d:Tap G n)(f:Shard G n):= {X with
   softer:= Shard.mix X.softer f.places
   sites:= (Shard.adds (powder X d) f).sites }
def cup (d:Tap G n)(f:Shard G n):={d with logarithm:= Shard.mix d.logarithm f.lens }
section
variable {X:Pipes G n}{d:Tap G n}{f:Shard G n}
lemma cup_rates {κ₀ k c a A δ b:ℝ}{u:ℕ →ℝ} (hX: (X.pours d).Valid p δ b) (hf:f.Wins p c) (he:(powder X d).Wins p k) (hK:Payments.hardCost p X u A) (hp:∀ i U, ‖d.forced i U‖ ≤ u i) (h:Payments.Rates p.B a A (k+c) κ₀): Ingredients (wood X d f) (cup d f) p δ a:=by
    let w:= wood X d f; let t:= cup d f; have hv: (powder w t).Wins p (k+c):= Shard.advances he hf
    obtain ⟨v,hh,hp',hh'⟩:= hv.wields
    exact Payments.tender ⟨hX.regular,hX.forced,hX.moves,hv.forces,hv.steady,hv.looks,hv.measurable,hv.carries⟩ hX.boundE hK ⟨hh,hh'⟩ (fun i U=> ⟨hp i U,hp' i U⟩) h
end
variable {X:Listing G n} {v:Collection.Source G n} {S : PathData G}{c:Clip} {f : Shard G n} {H w z α σ C Λ : ℝ} (g:G.Simple)
include g
lemma powdering (hn : 20 < n.val)
    (h : S.Bounds c σ C Λ) (hv : Local X p v H w) (hc : WilsonStartup.Decent c p)
    (he : Geo.Width p c σ) :
    let t:= branch X S c p v α
    let k:= softNeed G p c σ C α H
    (powder (shelves X S p) t).Wins p k := by
   intro t k; let Y:= shelves X S p
   let D:= delta (X.read v)
   let T:= hv.fittings g h hc hn α D
   obtain ⟨u,hu,hv'⟩:=hv.cheap
   have hx := Local.quote_soft (R:=S) (c:=c) g α D hu hv.smooth
   exact ⟨T.visits,T.steady,T.looks,T.reads,T.carries, _,fun i=> (norm_nonneg _).trans (hx (numbering _ i) 1), fun i U=> hx (numbering _ i) U, fun i=> Cost.equiv (numbering _) ((Local.quote_family h hc he α D hu hv' (delta_bound g hv.projects)).2 i)⟩

def wheel (S : PathData G) (c : Clip) (p : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)
    (α τ β : ℝ) (f:Shard G n) : RG.Rep G n :=
    let D:= delta (X.read v)
    let t:= Reset.reserve S c p X v α D
    let b:= shelves X S p
    finish S c p (wood b t f) (cup t f) (β+D) (Collection.vac v τ)
lemma wheel_board {γ : ℝ} (hn : 20 < n.val) (h : S.Bounds c σ C Λ) (hv : Local X p v H w) (hc : WilsonStartup.Decent c p)
    (he : Geo.Width p c σ) {A κ : ℝ} (hp : f.Wins p z)
    (hh : softNeed G p c σ C α H ≤ A) (hk : Payments.Rates p.B γ w (A+z) κ) :
    let D := delta (X.read v); let Y := shelves X S p; let t:=Reset.reserve S c p X v α D
    Ingredients (wood Y t f) (cup t f) p (regularNeed G p c σ C 0 H) γ := by
   intro D Y t
   obtain ⟨k,hvK,hK⟩:= hv.expensive
   have hu : (powder Y t).Wins p A:= Shard.Wins.income (powdering (α:=α) g hn h hv hc he) hh
   let D':= regularNeed G p c σ C 0 H
   have hv' : (Y.pours t).EBound p D' := by
      obtain ⟨u,hl,hK⟩:= hv.cheap
      change (Y.pours (fill X S c p v 0 D)).EBound ..
      exact ⟨_,fun i=> Local.quote_regular g h hc 0 D hl hv.smooth (numbering _ i), fun x=> Cost.equiv (numbering _) ((Local.quote_family h hc he 0 D hl hK (delta_bound g hv.projects)).1 x)⟩
   let v':Payments.Fittings (fill X S c p v 0 D) Y p:= hv.fittings g h hc hn ..
   have hy: (Y.pours t).KBound p w:= ⟨k,hvK,Payments.drop_reserve p (fun i=> (X.hard i).support) (fun i=> (hvK i).1) hK⟩
   exact cup_rates (f:=f) ⟨v'.regular, v'.support, v'.moves,hv',hy⟩ hp hu ⟨fun i=> (hvK i).1,hK⟩ (fun i U=> (hvK i).2 U) hk

omit g
lemma equal_stamp (X:Pipes G n)(d:Tap G n)(S:PathData G)(c:Clip)(p:BudgetPoint)(β τ : ℝ) (U:Config G n):
    (finish S c p X d β τ).exponent U=(trunk S c p X d β τ).exponent U:=by
   let hx := preserves X d p
   change τ * _ - _ - ((drawer G n).pours (widen X d)).additive p U=τ * _ - _ - _
   rw [hx.same_sum]; rfl

def old (S:PathData G)(c:Clip)(X:Listing G n)(v:Collection.Source G n)(p:BudgetPoint)(α β τ:ℝ) U:=
  (frozen X S c p v β τ).exponent U-α*receipt S c p U
def residualE (S:PathData G)(c:Clip)(X:Listing G n)(v:Collection.Source G n)(p:BudgetPoint)(α β τ:ℝ) U :=
   old S c X v p α (β-α) τ U-α*Reset.leading S p U
lemma appearing (S:PathData G)(c:Clip)(X:Listing G n)(v:Collection.Source G n)(p:BudgetPoint)(α β τ:ℝ) U:
   earlyValue X S c p v β τ α U = Real.exp (old S c X v p α β τ U)*(X.read v).gas p U:= by
   change _ * Real.exp (-α*receipt S c p U)=_
   unfold Rep.eval old; rw [Real.exp_sub]; dsimp only [frozen]; rw [neg_mul,Real.exp_neg,div_eq_mul_inv]; ring
include g
lemma jot (hn : 20 < n.val) (h:S.Bounds c σ C Λ) (hv : Local X p v H w) (hc : WilsonStartup.Decent c p)
    (he : Geo.Width p c σ) (τ β : ℝ)(f:Shard G n) : ∀ U,
    let r:= wheel S c p X v α τ β f
    let t := powder (shelves X S p) (branch X S c p v α)
    r.exponent U+t.read U=residualE S c X v p α β τ U := by
   intro U r t; let D:= delta (X.read v)
   let A:=Reset.reserve S c p X v α D; let T:= wood (shelves X S p) A f
   have hz:= hv.exponent g h hc he α hn (β-α) τ U
   rw [sub_add_cancel] at hz
   dsimp only at hz
   unfold r wheel; rw [equal_stamp]; change (Collection.vac v τ*_ -_ - ((shelves X S p).pours A).additive p U)+_= _
   rw [Reset.pay_alpha (Δ:=D) g h hv]
   change _ + (∑' i, (fill X S c p v α D).logarithm i U)=_
   change Collection.vac v τ * _-S.inChannels c p (β+D) U -(_+_)+_= _;
   have he : Collection.vac v τ * Fintype.card (Site n) - S.inChannels c p (β+D) U - ((shelves X S p).pours (fill X S c p v α D)).additive p U + (∑' i, (fill X S c p v α D).logarithm i U)=old S c X v p α (β-α) τ U:=hz
   unfold residualE; linarith only [he]

lemma wheelValue (hn : 20 < n.val) (h:S.Bounds c σ C Λ) (hv : Local X p v H w) (hc : WilsonStartup.Decent c p)
    (he : Geo.Width p c σ) (τ β : ℝ) (hf: f.Wins p z)
    {δ γ : ℝ} (hp : let D:=delta (X.read v); let A:=Reset.reserve S c p X v α D; let T:=wood (shelves X S p) A f; Ingredients T (cup A f) p δ γ):
    ∀ U, (wheel S c p X v α τ β f).eval U = Real.exp (residualE S c X v p α β τ U+f.read U)*(X.read v).gas p U:=by
   intro U
   let A:= Reset.reserve S c p X v α (delta (X.read v)); let Y:= shelves X S p
   have hx: (Shard.adds (powder Y A) f).read U=(powder Y (branch X S c p v α)).read U+f.read U:= Shard.increased (powdering g hn h hv hc he) hf U
   unfold wheel; rw [hp.unshifted,RG.Rep.eval, ← equal_stamp, mul_right_comm, ← Real.exp_add]
   rw [show residualE S c X v p α β τ U= _ from (jot (α:=α) g hn h hv hc he τ β f U).symm]
   rw [add_assoc (wheel .. |>.exponent U) (powder .. |>.read U) (f.read U)] -- fix
   rw [← hx]; rfl
end YM.IterationFour.Shore

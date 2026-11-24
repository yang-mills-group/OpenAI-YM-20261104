import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation

/-!
# Affine extraction and nonlinear dollars at the uncertain kinetic reset

Special issue: the prereset comparison to the independent prescription may
have ALREADY taken care of updating the cubic and quartic channels with the
formal beta update. Don't charge O(leading shift) in the E error; use the
literal same masked terms to cancel (so the operation works pointwise, not
just on a globally good set).

Setup of local interface. α here is the supplied deterministic part of the
reset. Examples:
 * α = (formal beta increment through order R); `supplied` pays
   that increment on both the low kinetic receipt and the model higher
   (classical cubic and quartic) channels, leaving the clip on β.
 * RG03 can instead have already moved that increment to the prescribed
   CLIPPED base (with all costs on failed indicators, even far from affine).
   Then call with α=0 and β already updated by that formal increment.
Either way the loop prescription remains in `PathData.principal` with its
original prefactor. This module doesn't claim the local expansion INPUTS
can be supplied by RG01/03. It consumes such an (aligned, fully exact) early
species and performs affine and scalar extraction, mask and flag reset and
closes to full leftover `Activities.Valid`. All identities on real V, in
particular on bad fields. Return the *same* representation carrying these
properties for use with the kinetic wave test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum.Reset
open Function Set Lattice Wilson RG MeasureTheory
open AnalyticBridge VerifiedReset Collection Averaging Quotes Residual WilsonStartup Geo
open Ovens Progress.DirectedRecipe Extra.Iteration Topology
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
variable (W : PathData G) (c : Clip) (p : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)

/-- The exact mask convention on the prereset cubic+quartic path channel. -/
def leading (U : Config G n) := layer (fun d:High => summit W p d 0) U

/-- Already supplies α on these channels as well. -/
def supplied (β τ α : ℝ) (U : Config G n) : ℝ :=
    earlyValue X W c p v β τ α U * Real.exp (-α*leading W p U)

/-- Append the UNknown extra beta change to that representation. -/
def reserve (α Δ : ℝ) : Tap G n :=
    { fill X W c p v α Δ with regular := (fill X W c p v 0 Δ).regular }

def after (β τ α : ℝ) : RG.Rep G n :=
    let Δ := delta (X.read v)
    finish W c p (shelves X W p) (reserve W c p X v α Δ) (β+α+Δ) (vac v τ)

/-- The *remaining* hard budget to bill when the regular `α` issue
    has already been matched, i.e. still pay `softNeed α`. -/
def charge (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C α H w γ : ℝ) : Prop :=
    ∃ m κ, softNeed G p c σ C α H ≤ m ∧ Payments.Rates p.B γ w m κ

variable {W c p X v}
lemma allocated (g : G.Simple) {σ C Λ w H γ : ℝ} (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w) (hc : Decent c p)
    (he : Width p c σ) (α : ℝ) (hp : charge G p c σ C α H w γ) :
    Ingredients (shelves X W p) (reserve W c p X v α (delta (X.read v))) p
      (regularNeed G p c σ C 0 H) γ := by
  let Y:= shelves X W p; let Δ:= delta (X.read v)
  let T:= reserve W c p X v α Δ
  let Z:= fill X W c p v 0 Δ
  have hm :  p.threshold^2 * |Δ| ≤ H := delta_bound g hv.projects
  have hI := hv.renew g h hc he α hn
    (show Fees G p c σ C α H w (regularNeed G p c σ C α H) γ from ⟨le_rfl,hp⟩)
  obtain ⟨κ',b,u,d,hP,hQ⟩ := hI.pays
  have hE : (Y.pours T).EBound p (regularNeed G p c σ C 0 H) := by
    obtain ⟨u,hu,hb⟩ := hv.cheap
    change (Y.pours Z).EBound ..
    exact ⟨_,fun i=> Local.quote_regular g h hc 0 Δ hu hv.smooth (numbering _ i),fun x=>
      Cost.equiv (numbering _) ((Local.quote_family h hc he 0 Δ hu hb hm).1 x)⟩
  have hF := hv.fittings g h hc hn 0 Δ
  exact ⟨κ',b,u,⟨⟨hF.regular,hF.support,hF.moves,hE,d.stamp.boundK⟩,d.visits,d.pays,d.steady,d.looks,
    d.reads,d.carries⟩,⟨hP.margin,hP.certificate⟩,hQ⟩

/-- Cancel the printed cubic/quartic channels on their *actual* masks only. -/
lemma pay_alpha (g : G.Simple) {σ C Λ H w α Δ : ℝ}
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w) (U : Config G n) :
    let Y := shelves X W p
    let T := fill X W c p v α Δ
    let Z := reserve W c p X v α Δ
    (Y.pours Z).additive p U = (Y.pours T).additive p U + α * leading W p U := by
  intro Y T Z
  have he (a b : ℝ) : layer (upperFade W p a b) U=-(a+b) * leading W p U := by
    unfold leading
    rw [show upperFade (n:=n) W p a b = _ from funext (fun i=> funext fun V=>high_fade_eq a b V i),layer_scale]
  have hx := hv.additive g h 0 Δ U
  have hy := hv.additive g h α Δ U
  rw [he] at hx hy
  change ((shelves X W p).pours (fill X W c p v 0 Δ)).additive p U = _
  unfold Y T; linarith only [hx,hy]

lemma debited (g : G.Simple) {σ C Λ w H γ : ℝ} (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w) (hc : Decent c p)
    (he : Width p c σ) (α β τ : ℝ) (hp : charge G p c σ C α H w γ) :
    (after W c p X v β τ α).eval = supplied W c p X v β τ α := by
  have hQ:= allocated g hn h hv hc he α hp
  funext U
  unfold after
  rw [hQ.unshifted,supplied,← hv.raw_evaluator g h hc he α hn β τ U]
  let Δ:=delta (X.read v)
  let m:=β+α+Δ; let w:= vac v τ; let Y:=shelves X W p
  let a:= branch X W c p v α
  let t:= reserve W c p X v α Δ
  let V:= trunk W c p Y t m w
  let H:= trunk W c p Y a m w
  have hv : V.exponent U=H.exponent U+(-α*leading W p U) := by
    change _ - (Y.pours t).additive p U = _
    rw [pay_alpha g h hv U]; unfold V H
    dsimp only [RG.Rep.exponent,trunk,a,m,w,Δ,Y,branch,Collection.vac,Geo.Width]; ring
  change V.eval U * Real.exp _ = H.eval U * Real.exp _ * Real.exp _
  rw [RG.Rep.eval, hv, RG.Rep.eval,Real.exp_add]
  change _ * Real.exp (∑' i, a.logarithm i U)= _ * _
  rw [show V.activities.gas V.p U = H.activities.gas H.p U from rfl]
  ring
end YM.IterationFour.Vacuum.Reset

import YM.Integration.LocalComparisonPreReset

/-! The native reset trunk before forced fusion. Its original forced family
already has a bound; the soft logarithm is retained exactly and vanishes on
unflagged fields. This gives a lawful representative for kinetic germ tests
without asserting a global replacement of the physical density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.VacuumGermReset
open Function Set Lattice Wilson RG MeasureTheory
open AnalyticBridge VerifiedReset Collection Averaging Quotes Residual WilsonStartup Geo
open Ovens Progress.DirectedRecipe Extra.Iteration Topology
open IterationFour.Vacuum
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def shell (W : PathData G) (c : Clip) (p : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (β τ α : ℝ) : RG.Rep G n :=
  trunk W c p (shelves X W p)
    (Reset.reserve W c p X v α (delta (X.read v)))
    (β+α+delta (X.read v)) (vac v τ)

variable {W : PathData G} {c : Clip} {p : BudgetPoint} {X : Listing G n}
    {v : Collection.Source G n} {σ C Λ H w : ℝ}

lemma lawful (g : G.Simple) (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w)
    (hc : Decent c p) (he : Width p c σ) (β τ α : ℝ) :
    (shell W c p X v β τ α).Lawful σ C Λ
      (regularNeed G p c σ C 0 H) w := by
  let Y := shelves X W p
  let Δ := delta (X.read v)
  have hm : p.threshold^2 * |Δ| ≤ H := delta_bound g hv.projects
  have hF := hv.fittings g h hc hn 0 Δ
  have hE : (Y.pours (fill X W c p v 0 Δ)).EBound p
      (regularNeed G p c σ C 0 H) := by
    obtain ⟨u,hu,hb⟩ := hv.cheap
    exact ⟨_,fun i => Local.quote_regular g h hc 0 Δ hu hv.smooth (numbering _ i),
      fun x => Cost.equiv (numbering _)
        ((Local.quote_family h hc he 0 Δ hu hb hm).1 x)⟩
  have hK : (Y.pours (fill X W c p v 0 Δ)).KBound p w := by
    obtain ⟨k,hk,hK⟩ := hv.expensive
    exact ⟨k,hk,Payments.drop_reserve p (fun i => (X.hard i).support)
      (fun i => (hk i).1) hK⟩
  exact ⟨h,⟨hF.regular,hF.support,hF.moves,hE,hK⟩⟩

lemma raw_eval (g : G.Simple) (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w)
    (hc : Decent c p) (he : Width p c σ) (β τ α : ℝ) (U : Config G n) :
    (shell W c p X v β τ α).eval U *
      Real.exp (∑' i, (Reset.reserve W c p X v α (delta (X.read v))).logarithm i U) =
      Reset.supplied W c p X v β τ α U := by
  rw [Reset.supplied,← hv.raw_evaluator g h hc he α hn β τ U]
  let Δ := delta (X.read v)
  let m := β+α+Δ
  let w := vac v τ
  let Y := shelves X W p
  let a := branch X W c p v α
  let t := Reset.reserve W c p X v α Δ
  let V := trunk W c p Y t m w
  let T := trunk W c p Y a m w
  have hx : V.exponent U = T.exponent U + (-α*Reset.leading W p U) := by
    change _ - (Y.pours t).additive p U = _
    rw [Reset.pay_alpha g h hv U]
    unfold V T
    dsimp only [RG.Rep.exponent,trunk,a,m,w,Δ,Y,branch,Collection.vac,Geo.Width]
    ring
  change V.eval U * Real.exp _ = T.eval U * Real.exp _ * Real.exp _
  rw [RG.Rep.eval,hx,RG.Rep.eval,Real.exp_add]
  change _ * Real.exp (∑' i, a.logarithm i U) = _ * _
  rw [show V.activities.gas V.p U = T.activities.gas T.p U from rfl]
  ring

lemma good_eval (g : G.Simple) (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w)
    (hc : Decent c p) (he : Width p c σ) (β τ α : ℝ)
    (U : Config G n) (hU : flags p.threshold U = ∅) :
    (shell W c p X v β τ α).eval U = Reset.supplied W c p X v β τ α U := by
  have hF := hv.fittings g h hc hn α (delta (X.read v))
  have hz (i : ℕ) :
      (Reset.reserve W c p X v α (delta (X.read v))).logarithm i U = 0 := by
    by_contra hi
    exact hF.visits i U hi (by simp [Healthy,hU])
  have hh := raw_eval g hn h hv hc he β τ α U
  simp only [hz,tsum_zero,Real.exp_zero,mul_one] at hh
  exact hh

lemma rendered_lawful (g : G.Simple) (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w)
    (hc : Decent c p) (he : Width p c σ) (β τ α : ℝ)
    (S : List (Piece G n)) (k : Piece G n → ℝ) (hS : Render.permits S p) :
    (Render.append S (shell W c p X v β τ α) k).Lawful σ C Λ
      (regularNeed G p c σ C 0 H + Render.dollars (fun i => ‖k i‖) S) w :=
  ⟨h,Render.addition k hS (lawful g hn h hv hc he β τ α).labels⟩

lemma rendered_good_eval (g : G.Simple) (hn : 20 < n.val)
    (h : W.Bounds c σ C Λ) (hv : Local X p v H w)
    (hc : Decent c p) (he : Width p c σ) (β τ α : ℝ)
    (S : List (Piece G n)) (k : Piece G n → ℝ) (hS : Render.permits S p)
    (U : Config G n) (hU : flags p.threshold U = ∅) :
    (Render.append S (shell W c p X v β τ α) k).eval U =
      (LocalComparison.PreReset.append S W c p X v β τ α k).eval U := by
  rw [Render.generated k hS (lawful g hn h hv hc he β τ α).labels U,
    LocalComparison.PreReset.append_eval S W c p X v β τ α k h
      (fun U => LocalComparison.PreReset.series_of_EBound hv.unweighted U)
      (fun a ha U => LocalComparison.PreReset.payload_series (hS a ha) (X.read v) U) U,
    good_eval g hn h hv hc he β τ α U hU]
  rfl

end YM.Integration.VacuumGermReset
end

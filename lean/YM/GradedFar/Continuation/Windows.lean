import YM.GradedFar.Clock

/-!
# Moving T quantifiers, for the continuation

Pure filter geometry. A *fixed* sufficiently large threshold in T is OK in (M.2).
And not a fixed upper compact; use all T through the indicated growing range.
-/
namespace YM.FVA2.GradedFar
namespace Continuation
noncomputable section
open Filter Set Real Topology
open scoped Topology

-- τ for radii tending to zero from above, use the project's `gYM`.
local notation "τ" => 𝓝[>] (0:ℝ)
abbrev Window := ℝ × ℝ
namespace Window
def len (x : Window) : ℝ := x.1
/-- log T. -/
def sep (x : Window) : ℝ := x.2

def Stretch (x : Window) : ℝ := exp x.2
def Coarse (x : Window) : ℝ := x.1*x.Stretch

/-- All windows in the given span. -/
def windows (Q : Set Window) := (τ ×ˢ (atTop : Filter ℝ)) ⊓ principal Q
lemma windows_eventually (Q : Set Window) (p : Window → Prop) :
    (∀ᶠ w in windows Q, p w) ↔ ∃ s₀ : ℝ, ∀ᶠ r in τ, ∀ s ≥ s₀, (r,s) ∈ Q → p (r,s) := by
  rw [windows,eventually_inf_principal]
  constructor
  · intro h
    obtain ⟨x,hx,y,hy,h⟩ := Filter.eventually_prod_iff.mp h
    obtain ⟨s,hv⟩ := eventually_atTop.1 hy
    exact ⟨s,hx.mono fun r hr q hq => h hr (hv q hq)⟩
  rintro ⟨s,h⟩
  exact Filter.eventually_prod_iff.mpr ⟨_,h,(fun q : ℝ => s ≤ q), eventually_ge_atTop _,fun {_} p {j} q => p j q⟩

lemma windows_separation (Q : Set Window) : Tendsto Window.sep (windows Q) atTop :=
  tendsto_snd.mono_left inf_le_left
lemma windows_short (Q : Set Window) : Tendsto Window.len (windows Q) τ :=
  tendsto_fst.mono_left inf_le_left
lemma windows_span (Q : Set Window) : ∀ᶠ w in windows Q, w ∈ Q :=
  (le_principal_iff.mp (show windows Q ≤ principal Q from inf_le_right))
lemma windows_le {P Q : Set Window} (h : P ⊆ Q) : windows P ≤ windows Q :=
  inf_le_inf_left _ (principal_mono.mpr h)
end Window

-- B real, include cutoff multiplier C even if not needed for one call
/-- Exactly M.1 upper bound. Eventually uniform quantifiers taken with a Price that can enlarge its T threshold *for such lease*. -/
def upper (G : Gauge) (C B : ℝ) : Set Window := {q | q.Stretch ≤ C * gYM G q.len ^ (-B)}
def lower (G : Gauge) (C B : ℝ) : Set Window := {q | C * gYM G q.len ^ (-B) ≤ q.Stretch}
def band (G : Gauge) (c C B : ℝ) : Set Window := upper G C B ∩ lower G c B
lemma narrower (G : Gauge) (c C B : ℝ) : Window.windows (band G c C B) ≤ Window.windows (upper G C B) :=
  Window.windows_le inter_subset_left

/-- A compact setup: if `upper` and `2≤ exp s0`, one can freeze s at s0 to use
(large-threshold) window estimates provided s0 meets their threshold. Not an inference
`Tendsto` s0→∞ along τ.
-/
lemma has_room {G : Gauge} (simple : G.Simple) (C B : ℝ) (hC : 0<C) (hB : 0<B) (T : ℝ) :
    ∀ᶠ r in τ, T ≤ C * gYM G r ^ (-B) := by
  have hx : Tendsto (fun r : ℝ => C * gYM G r^(-B)) τ atTop := (show Tendsto
    (fun r => gYM G r ^ (-B)) τ atTop from
    (tendsto_rpow_neg_nhdsGT_zero (by linarith)).comp (tendsto_nhdsWithin_iff.mpr
      ⟨shrink simple,positive_g simple⟩)).const_mul_atTop hC
  exact hx.eventually_ge_atTop T
end
end Continuation
end YM.FVA2.GradedFar

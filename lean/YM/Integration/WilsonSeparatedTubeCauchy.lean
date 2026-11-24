import YM.Integration.WilsonSeparatedTubeEnvelope
import Mathlib.Analysis.Complex.Liouville

/-! Cauchy estimates on a compact subset of the complex tube, for the true finite mixed roster.
The same disc and the same scale envelope work at every derivative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedTubeCauchy
open Function Filter Set Metric Extraction Spec Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) {l : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}

private theorem disc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x v : E} {g : E → ℂ} {ρ M : ℝ}
    (hρ : 0 < ρ) (hv : ‖v‖≤1) (ha : AnalyticOnNhd ℂ g (closedBall x ρ))
    (hm : ∀ y∈closedBall x ρ, ‖g y‖≤M) (j : ℕ) :
    ‖iteratedDeriv j (fun t : ℂ=>g (x+t • v)) 0‖ ≤ j.factorial * M / ρ^j := by
  let a (t : ℂ) := x+t • v
  have dc : Differentiable ℂ a := by unfold a; fun_prop
  have inside : MapsTo a (closedBall 0 ρ) (closedBall x ρ) := by
    intro t ht
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    have ht' : ‖t‖≤ρ := by simpa using ht
    dsimp only [a]
    rw [add_sub_cancel_left,norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg t) hv).trans ht'
  have df := ha.differentiableOn.comp dc.differentiableOn inside
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hρ
    ⟨df.mono ball_subset_closedBall,df.continuousOn.mono closure_ball_subset_closedBall⟩
    (fun z hz=>hm _ (inside (sphere_subset_closedBall hz)))

private lemma hol_jet {g : ℂ → ℂ} {x : ℂ} (h : AnalyticAt ℂ g x) (j : ℕ) :
    AnalyticAt ℂ (iteratedDeriv j g) x := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem real_jet {g : ℂ → ℂ} {x : ℝ} (ha : AnalyticAt ℂ g (x:ℂ)) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ=>g t) x = iteratedDeriv j g (x:ℂ) := by
  induction j generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
    have ex : ∀ᶠ t : ℝ in 𝓝 x, AnalyticAt ℂ g (t:ℂ) :=
      (Complex.continuous_ofReal.continuousAt : ContinuousAt (fun t : ℝ=>(t:ℂ)) x).eventually ha.eventually_analyticAt
    have same : iteratedDeriv j (fun t : ℝ=>g t) =ᶠ[𝓝 x] fun t : ℝ=>iteratedDeriv j g (t:ℂ) :=
      ex.mono fun _ h=>ih h
    rw [iteratedDeriv_succ,iteratedDeriv_succ]
    exact same.deriv_eq.trans (hol_jet ha j).differentiableAt.hasDerivAt.comp_ofReal.deriv


/-- The field and order of the roster may be chosen after the scale; the constants are prepaid. -/
theorem complex (hG : G.Simple) (bliss : Bliss F l Z H) (L : Almanac F) {n : ℕ}
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (K : Set (Full n)) (hk : IsCompact K) (ht : K ⊆ tube n) :
    ∃ ρ : ℝ, 0<ρ ∧ ∃ δ∈Ioc (0:ℝ) 1, ∃ A : ℝ, 0≤A ∧ ∃ p : ℕ,
    ∀ᶠ r in trail, ∀ (σ : Equiv.Perm (Fin n)) (u : ∀ i,S.Field (d (σ i))),
      (∀ i, Ascent.cost F (d (σ i)) r (u i) ≤ B) →
      ∀ (i : Survey F) (D : ∀ k, Blanket k) (X : (Survey.reads L i).world.Aurora D)
        (x : Full n), x∈K → ∀ v : Full n, ‖v‖≤1 → ∀ j : ℕ,
      ‖iteratedDeriv j (fun t : ℂ=>weather X (WilsonSeparatedTubeEnvelope.tag u)
        r (x+t • v)) 0‖ ≤ j.factorial * (A*(LogV r/δ)^p) / ρ^j := by
  obtain ⟨ρ,hρ,inside⟩ := hk.exists_cthickening_subset_open (south n) ht
  have compact : IsCompact (cthickening ρ K) := hk.cthickening
  obtain ⟨δ,⟨clear,hδ⟩,hle⟩ := (((Room.compact compact inside).and
    (show ∀ᶠ d : ℝ in trail, 0<d from self_mem_nhdsWithin)).and
    ((ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨A,hA,p,earn⟩ := WilsonSeparatedTubeEnvelope.purchased F hG bliss L d hB
  refine ⟨ρ,hρ,δ,⟨hδ,hle⟩,A,hA,p,?_⟩
  filter_upwards [earn] with r hr
  intro σ u bound i D X x hx v hv j
  have closed : closedBall x ρ ⊆ cthickening ρ K := fun y hy=>mem_cthickening_of_dist_le _ x ρ K hx hy
  obtain ⟨analytic,price⟩ := hr σ u bound i D X
  exact disc hρ hv (analytic.mono (closed.trans inside)) (fun z hz=>price δ ⟨hδ,hle⟩ z (clear z (closed hz))) j

end YM.Integration.WilsonSeparatedTubeCauchy

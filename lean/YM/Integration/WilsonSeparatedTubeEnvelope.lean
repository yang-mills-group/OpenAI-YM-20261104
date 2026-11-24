import YM.GapsContact.Tube.Scale

/-! A single physical complex tube envelope for an arbitrary finite mixed-grade roster.
At each physical radius both the fields and their order may vary. Only their actual
reflected two-point costs enter the bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedTubeEnvelope
open Function Filter Set Metric Extraction Spec Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) {l : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}

/-- Pinned source labels for the original finite array at the true degrees. -/
def tag {n : ℕ} {d : Fin n → ℕ} (v : ∀ i,S.Field (d i)) := fun i => S.pin (d i) (v i)

theorem purchased (hG : G.Simple) (bliss : Bliss F l Z H) (L : Almanac F) {n : ℕ}
    (d : Fin n → ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ᶠ r in trail, ∀ (σ : Equiv.Perm (Fin n))
      (u : ∀ i,S.Field (d (σ i))), (∀ i, Ascent.cost F (d (σ i)) r (u i) ≤ B) →
      ∀ (i : Survey F) (D : ∀ k, Blanket k) (X : (Survey.reads L i).world.Aurora D),
      AnalyticOnNhd ℂ (weather X (tag u) r) (tube n) ∧ ∀ δ ∈ Ioc (0:ℝ) 1,
      ∀ z : Full n, Room (shade z) δ → ‖weather X (tag u) r z‖ ≤ A*(LogV r/δ)^p := by
  choose roof a m hroof ha sky using fun i => Ascent.opened_sky F hG bliss (d i)
  let rate (i : Fin n) := a i ^ 2 * (8:ℝ)^(2*m i)*B
  refine ⟨∏ i,rate i,Finset.prod_nonneg (fun i _ => by dsimp [rate]; positivity),∑ i,2*m i,?_⟩
  have roofs : ∀ᶠ r in trail, ∀ i,r ≤ roof i := eventually_all.mpr fun i =>
    (ge_mem_nhds (hroof i)).filter_mono nhdsWithin_le_nhds
  filter_upwards [roofs,self_mem_nhdsWithin (a:=0),
    (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r hrRoof hr hu
  intro σ u bound i D X
  refine ⟨hollow X (observe L i X).2 _ r hr,?_⟩
  intro δ hd z hz
  have scal : Room (shade ((r:ℂ) • z)) (r*δ) := by
    rw [← valley z,← glow_scales,im_glow]
    exact hz.mul hr.le
  have price := enough_fields L i X (d:=fun j => d (σ j)) u ⟨hr,hu⟩ hd
    (R:=fun j=>roof (σ j)) (A:=fun j=>a (σ j)) (m:=fun j=>m (σ j))
    (fun j=>sky (σ j)) (fun j=>hrRoof (σ j)) _ scal
  refine price.trans ?_
  let t := LogV r / δ
  calc
    ∏ j : Fin n, a (σ j)^2*(8*t)^(2*m (σ j))*Ascent.cost F (d (σ j)) r (u j)
        ≤ ∏ j : Fin n, rate (σ j)*t^(2*m (σ j)) := by
            apply Finset.prod_le_prod
            · intro j _; exact mul_nonneg (mul_nonneg (sq_nonneg _) (by rw [pow_mul]; positivity)) (Ascent.cost_pos ..)
            · intro j _
              calc _ ≤ a (σ j)^2*(8*t)^(2*m (σ j))*B :=
                        mul_le_mul_of_nonneg_left (bound j) (mul_nonneg (sq_nonneg _) (by rw [pow_mul]; positivity))
                   _ = _ := by dsimp only [rate]; rw [mul_pow]; ring
    _ = ∏ j : Fin n, rate j*t^(2*m j) := Equiv.prod_comp σ (fun j=>rate j*t^(2*m j))
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

end YM.Integration.WilsonSeparatedTubeEnvelope

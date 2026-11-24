import YM.Integration.WilsonPhysicalHistoryGalleryHaar
import YM.Integration.WilsonAllDateHarvestClearTransfer

/-! Preserve the full previously filed source in the original Wilson conditional.
The original charged sheet buys the retained integrand on every configuration.
On a registered marker course its field-independent factor follows the genuine
licensed maps at all earlier dates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFiledGallery
open Function Finset Lattice Wilson RG Source Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory RG05Readout RG05Readout.Many
open WilsonPhysicalHistoryPictureRestore WilsonAllDateHarvestClearTransfer
open scoped Classical BigOperators

variable {I J : Type} [Countable I] [Countable J] {G : Gauge} {C : Family G}
  {per i N : ℕ} {L : Side} {x e κ w b₀ b₁ z Y Γ K : ℝ} {T : Type*} {A₀ : Teller G}
  {Q : ConnectedActivityE6.Target G A₀} {horizon : ConnectedActivityE6.Target.Order G w}
variable {tube : Pressure.Tube G (C.path.levels.clock.op i per)} (cash : Cash w x κ L Q horizon z tube (C.path.rep N per (i+1)))
  {k : ℕ} (eyes : Eyes cash (C.path.rep N per i) e Γ Y K k)
  {a q h : ℝ}

section
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {o : V → Site (C.side (i+1) per)}
  (A : Gallery T I o (C.path.rep N per (i+1)) R) (previous : Lamps T J G (C.path.rep N per (i+1)).p o R) (weights : V → ℝ)
  (grant : Seal (picture A previous) weights b₀ b₁) (positive : ∀ v, 0 < weights v)
  (slots : HasSlots (C.path.rep N per (i+1)).p (C.path.rep N per (i+1)).activities) (fits : 2*(b₀+b₁) ≤ K)
  (ω : V → ℝ) (pos : ∀ v, 0 < ω v) (expo : 0 ≤ a)
  (reg : A.E.Paid ω (C.path.rep N per (i+1)).p.B (a+2) q) (hard : A.K.Paid ω (C.path.rep N per (i+1)).p.B a h)
include cash eyes grant positive slots fits pos expo reg hard in
theorem pushed (t : T) :
    (C.path.levels.clock.op i per).push (C.path.rep N per (i+1)).beta ((picture A previous).density t) = fun U =>
      Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t) * (C.path.levels.clock.op i per).push (C.path.rep N per (i+1)).beta (retained A previous t) U := by
  have admitted := WilsonPhysicalHistoryGalleryHaar.charged cash eyes A previous weights grant positive slots fits
    ω pos expo reg hard t
  rw [funext admitted.2]
  exact amp_live (LinearMap.mulLeft ℂ _) (C.path.levels.clock.op i per) admitted.1 (C.path.levels.transition_mass i per (C.path.rep N per (i+1)).beta)
end

section
variable {n b : ℕ} {V : ℕ → Type} [∀ j, DecidableEq (V j)] [Fintype (V (i+1))] {W : Type*}
  {R : ∀ j, Census (V j)} {route : Planner C per n V W} {cut : W → ℕ}
  (A : Gallery T I (route.supportX (i+1)) (C.path.rep N per (i+1)) (R (i+1)))
  (previous : Lamps T J G (C.path.rep N per (i+1)).p (route.supportX (i+1)) (R (i+1))) (weights : V (i+1) → ℝ)
  (grant : Seal (picture A previous) weights b₀ b₁) (positive : ∀ v, 0 < weights v)
  (slots : HasSlots (C.path.rep N per (i+1)).p (C.path.rep N per (i+1)).activities) (fits : 2*(b₀+b₁) ≤ K)
  (ω : V (i+1) → ℝ) (pos : ∀ v, 0 < ω v) (expo : 0 ≤ a)
  (reg : A.E.Paid ω (C.path.rep N per (i+1)).p.B (a+2) q) (hard : A.K.Paid ω (C.path.rep N per (i+1)).p.B a h)
include cash eyes grant positive slots fits pos expo reg hard in
theorem enrolled (t : T) {nb : n ≤ b} (bi : b ≤ i+1) (iN : i+1 ≤ N)
    {X : ∀ j, Config G (C.side j per) → Poly (R j)}
    (full : Replay route cut nb (i+1) X N) (filed : X (i+1) = (picture A previous).density t) :
    ∃ F : ∀ j, Config G (C.side j per) → Poly (R j), ∃ track : Replay route cut nb (i+1) F N,
      F (i+1) = retained A previous t ∧ ∀ j (bj : b ≤ j) (ji : j ≤ i+1) (U : Config G (C.side j per)),
        X j U = carried track (Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t)) j bj ji * F j U := by
  have admitted := WilsonPhysicalHistoryGalleryHaar.charged cash eyes A previous weights grant positive slots fits
    ω pos expo reg hard t
  obtain ⟨F, track, born⟩ := reels_write (A:=route) (H:=R) (s:=cut) nb bi
    (fun j bj ji => (full.downhill j bj ji).choose) (retained A previous t) N
  refine ⟨F, track, born, fun j bj ji U => across track _ full iN (born ▸ admitted.1) ?_ bj ji U⟩
  intro field
  rw [filed, born]
  exact admitted.2 field
end
end YM.Integration.WilsonAllDateHarvestFiledGallery


import YM.RG17.Aperture

set_option autoImplicit false
noncomputable section

namespace PhysicalMatching.H7StandaloneTranslatedCompactRoom
open YM
open Function Set OPE Orbits RG17.Profile

variable {n : ℕ}

def translated (r : ℝ) (x : Points n) (o : E4) : Points n :=
  WithLp.toLp 2 (fun i : Fin n => o + r • x.ofLp i)

theorem publicChart (r : ℝ) (x : Points n) (o : E4) :
    (translated r x o).ofLp = liftAt r x o := by
  funext i
  change o + r • x.ofLp i = r • x.ofLp i + o
  exact add_comm _ _

theorem moved {M η : ℝ} (r : ℝ) (x : Points n) (o : E4)
    (hr : 0 ≤ r) (h : WithinRoom 1 M η x.ofLp (0 : E4)) :
    WithinRoom r M η (translated r x o).ofLp o := by
  rw [publicChart]
  exact around x r o hr h

theorem original {K : Set (Points n)} (hk : IsCompact K) (hs : K ⊆ conf n) :
    ∃ M η : ℝ, 0 ≤ M ∧ 0 < η ∧ ∀ r : ℝ, 0 ≤ r → ∀ x ∈ K, ∀ o : E4,
      WithinRoom r M η (translated r x o).ofLp o := by
  obtain ⟨M, η, hM, hη, room⟩ := finite_venue hk hs
  exact ⟨M, η, hM, hη, fun r hr x hx o => moved r x o hr (room x hx)⟩

end PhysicalMatching.H7StandaloneTranslatedCompactRoom

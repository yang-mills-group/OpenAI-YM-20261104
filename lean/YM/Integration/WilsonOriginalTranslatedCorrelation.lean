import YM.Integration.WilsonOriginalGlobalViewerShape

/-! Translation and the empty input on the actual spectator of a filed run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTranslatedCorrelation
open Lattice Wilson RG Source Extraction Spec Trace.Pilot PhysMS OPE
open scoped Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S)
theorem original (who : Viewers F) (J : tower S) {n : ℕ} (d : Fin n → ℕ)
    (v : MaxwellSlots C d) (s : ℝ) (hs : 0 < s) (o : E4) {x : Points n} (hx : x ∈ conf n) :
    S.classMoment (spectator F who) d (points fun i => o + s • x i) (fun i => J (d i) (v i)) =
      measured F who J v s x := by
  let token : Fin n → C.book.Token := fun i => ⟨d i, S.representative (d i) (J (d i) (v i))⟩
  have h := (spectate F who).translations n (s • x) (Work.A05.smul_conf hs hx) o token
  have e : Points.across o (s • x) = points (fun i => o + s • x i) := by
    ext i
    exact congrArg (fun t : E4 => t _) (add_comm (s • x _) o)
  rw [e] at h
  exact h

theorem empty (who : Viewers F) (J : tower S) (d : Fin 0 → ℕ) (v : MaxwellSlots C d)
    (s : ℝ) (x : Points 0) : measured F who J v s x = 1 :=
  (spectate F who).laws.trivial (fun i => ⟨d i,S.representative (d i) (J (d i) (v i))⟩) (s • x)
end YM.Integration.WilsonOriginalTranslatedCorrelation

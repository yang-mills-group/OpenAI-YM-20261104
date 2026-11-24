import YM.Integration.WilsonIndependentFreshReel
import YM.RegulatorIR.Profiles.Trek

/-! The chronological vacuum alone supplies the upper range for an independent
insertion born later. A zero earlier mark preserves its actual hidden law. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentFreshQuietReel
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Uniform
open RegulatorIR.Ward RegulatorIR.Profiles RegulatorIR.Prim PertExtension Series.Tested PowerSeries
open scoped Topology ContDiff
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}

theorem priorZero (G : Gauge) : BasisT 0 0 (0 : Portrait G) 0 := by
  refine ⟨⟨continuous_const,fun _ _ _ => rfl,?_⟩,?_,?_,?_⟩
  · intros
    exact contDiffAt_const
  · intro i r
    change (Function.support (0 : Packet (Foot G) r)).Finite
    simp
  · intro e r x z
    rfl
  · intro v
    change tale (fun _ : ℝ => (0:ℝ)) = _
    rw [tale_const,map_zero,pow_zero,one_mul]
    ext1 i
    simp [shelter,drums,strum]

variable (H : Reel S) (T : S.Accounts) (quiet : H.Follows T)
  (E : Era M) {L : Meter W} {p b m s : ℕ} (B : S.Primitive L p b)
  (Z : (E.part S T B).Report m) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))

include quiet stamp in
theorem issued : ∃ measured : W → ℝ → ℝ,
    (∀ j : Page E.spans, Nonempty (RangeR G (n (E.page j)) (H.spot (E.page j))
      (measured j.bindW) s m (T.orb (E.page j)) (Z.point j))) ∧
    (∀ (j : Page E.spans) (x y : ℝ → Horizon G (n (E.page j))),
      ContDiffAt ℝ ∞ x 0 → ContDiffAt ℝ ∞ y 0 → reel_prop x y →
      reel (Z.point j) m x = reel (Z.point j) m y) ∧
    ∀ w, Aspiration (measured w) (fun i => coeff i (PowerSeries.X ^ s *
      PowerSeries.mk ((E.expanse S).vista (E.part S T B) Z (WilsonIndependentFreshReel.margins H E) w))) := by
  let vac : T.Report 0 := declaring T (fun _ => 0) (fun _ _ _ h => (h rfl).elim)
  exact WilsonIndependentFreshReel.issued H T quiet vac (fun _ => 0) (fun _ => priorZero G)
    E B Z film stamp

end YM.Integration.WilsonIndependentFreshQuietReel

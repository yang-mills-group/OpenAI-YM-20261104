import YM.Integration.WilsonIndependentFreshWardBirth
import YM.RegulatorIR.Binding.Rosette
import YM.RegulatorIR.Ledger.Ages

/-! A fresh measuring word at a nonbare date traverses the subsequent genuine
finite Wick edges with the exact same old quiescent action at each date. The
range witness at its birth is obtained on the original traversal. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentFreshWardHistory
open RegulatorIR RegulatorIR.Binding RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Lattice RegulatorIR.Taping RegulatorIR.Geometry RegulatorIR.Laplace RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Uniform
open WilsonIndependentFreshWardBirth
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side}
  (S : Heir n G) (T : S.Accounts) (D : Docket S)
  {m₀ s₀ : ℕ} (old : T.Report m₀) (top : ∀ w : W, TopHooks n G w)
  (actual : Coverage T old D top s₀) (E : Era M)
  {m s : ℕ}
  (sub : (E.expanse S).Accounts) (agrees : ∀ j, sub.orb j = T.orb (E.page j))
  (Z : sub.Report m) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))

include actual agrees stamp in
theorem dated :
    ∃ measured : W → ℝ → ℝ, ∀ j : Page E.spans,
      Nonempty (RangeR G (n (E.page j)) (D.rates (E.page j)) (measured j.bindW)
        s m (T.orb (E.page j)) (Z.point j)) := by
  let page (w : W) := E.page (Page.opening E.spans w)
  let R (w : W) := (actual.craved T old D top (page w)).some
  let A (w : W) := hold (E := (R w).E) (vital (n (page w)) (film w))
  let measured (w : W) (t : ℝ) := rightSum (R w).Val (A w) t / rightSum (R w).Val 1 t
  refine ⟨measured,Page.proves ?_ ?_⟩
  · intro w
    have h := issued (R w) (stamp w) (Z.ceilingM w) (D.even (page w)) (D.connected (page w))
    have eq_ : Z.point (Page.opening E.spans w) = fun e r =>
        (Carto G _ _ (D.even (page w)) (D.connected (page w))).scroll
          (Z.main (Page.opening E.spans w) e r) := by
      funext e r
      rw [Z.same w e r]
      change (S.maps (page w)).scroll _ = _
      rw [D.compatible]
    rw [eq_]
    exact h
  · intro j prior
    obtain ⟨r⟩ := prior
    obtain ⟨coins⟩ := D.legs (E.wing j)
    rw [← Z.step_p j, agrees j.prev]
    change Nonempty (RangeR G _ _ _ _ _ (T.orb (E.wing j).next) _)
    rw [← T.step_o (E.wing j)]
    exact r.along (D.bushes (E.wing j)) (D.landscape (E.wing j))
      (D.even _) (D.even _) (D.teeth (E.wing j)) coins

variable {L : Meter W} {p b : ℕ}

include actual in
theorem original (B : S.Primitive L p b) (Z₁ : (E.part S T B).Report m) (word : W → Portrait G)
    (purchase : ∀ w, BasisT m s (word w) (Z₁.main (Page.opening E.spans w))) :
    ∃ measured : W → ℝ → ℝ, ∀ j : Page E.spans,
      Nonempty (RangeR G (n (E.page j)) (D.rates (E.page j)) (measured j.bindW)
        s m (T.orb (E.page j)) (Z₁.point j)) :=
  dated S T D old top actual E (E.part S T B) (fun _ => rfl) Z₁ word purchase

end YM.Integration.WilsonIndependentFreshWardHistory

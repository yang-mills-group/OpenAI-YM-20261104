import YM.Integration.WilsonCenteredNestedCalibration

/-! Compare the exact ordinary Wilson coefficient with an independently
priced finite nested program on the very same public reader. The measured
tree error and the signed change of its comparable coefficients have
different prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPhysical
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite
open Extraction Spec Table Filter WilsonCenteredNestedProgram WilsonCenteredNestedRates
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def vertexFee {n : ℕ} {p : Fin n → Tree} (s : (fork n p).Inner → ℝ)
    (v : (fork n p).Leaf → S.Tag) (D : (fork n p).Inner → ℕ) (m : ℕ)
    (L E : ℝ → ℝ) : ℝ :=
  (((premium F Q (fork n p) D s (fun _=>1) * ∏ i:(fork n p).Inner,L (s i)) * s (.inl ())^m) *
    leaves (fork n p) s (degrees v) (s (.inl ()))) * ∑ i:(fork n p).Inner,E (s i)

theorem original (paid : Nesting.Uniform F Q) (A : Rule F Q) (g L : ℝ → ℝ) (Ln : ∀ r,0 ≤ L r)
    (order : ℕ) (n : ℕ) (p : Fin n → Tree) (v : (fork n p).Leaf → S.Tag)
    (D : (fork n p).Inner → ℕ) (m : ℕ) (c : Q.channels m) (M η ε : ℝ)
    (Mn : 0 ≤ M) (ηp : 0 < η) (ep : 0 < ε) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s : (fork n p).Inner → ℝ) (z : (fork n p).Plot),
      Accept r M η s z → calibrated F Q A g L (fun a=>|g a|^order) (fork n p) s z v D m →
      ‖Kernel.output F Q z v c - run F Q A g (fork n p) s z v D m ⟨Fin.last m,c⟩‖ ≤
        bothToll (wages v) ε m D s + vertexFee F Q s v D m L (fun a=>|g a|^order) := by
  filter_upwards [paid.direct n p v m c D M η ε Mn ηp ep] with r atRadius
  intro s z accepted rows
  have base := (atRadius s z accepted).2.2.2
  have here : s (.inl ()) = r := accepted.scale
  have tp := accepted.levels
  rw [← here] at tp
  have sub := (WilsonCenteredNestedCalibration.original F Q A g L (fun a=>|g a|^order)
    Ln (fun a=>pow_nonneg (abs_nonneg _) _) (fork n p) s z v D m ⟨Fin.last m,c⟩ _ tp.1 tp rows).change
  rw [WilsonCenteredNestedProgram.chord,WilsonCenteredNestedRates.separated] at sub
  have tri := dist_triangle (Kernel.output F Q z v c) (Kernel.chord F Q z v c D)
    (run F Q A g (fork n p) s z v D m ⟨Fin.last m,c⟩)
  simp only [dist_eq_norm] at tri
  exact tri.trans (add_le_add base sub)

/-- One pre-radius threshold gives both the signed full-coefficient
comparison and the native norm and viewer bills for the full exterior law. -/
theorem with_viewers (paid : Nesting.Uniform F Q) (A : Rule F Q) (g L : ℝ → ℝ) (Ln : ∀ r,0 ≤ L r)
    (order : ℕ) (n : ℕ) (p : Fin n → Tree) (v : (fork n p).Leaf → S.Tag)
    (D : (fork n p).Inner → ℕ) (m : ℕ) (c : Q.channels m) (J : Type) [Fintype J] (w : J → S.Tag)
    (M η ε δ : ℝ) (Mn : 0 ≤ M) (ηp : 0 < η) (ep : 0 < ε) (dp : 0 < δ) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s : (fork n p).Inner → ℝ) (z : (fork n p).Plot) (y : J → E4),
      Accept r M η s z → Buffer z y δ →
      (‖Kernel.normData F Q z v m y w‖ ≤ toll (wages v) ε (m+1:ℝ) s ∧
        ∀ q : Viewers F,‖Kernel.pipe F Q z v q m y w‖ ≤ toll (wages v) ε (m+1:ℝ) s) ∧
      (calibrated F Q A g L (fun a=>|g a|^order) (fork n p) s z v D m →
        ‖Kernel.output F Q z v c - run F Q A g (fork n p) s z v D m ⟨Fin.last m,c⟩‖ ≤
          bothToll (wages v) ε m D s + vertexFee F Q s v D m L (fun a=>|g a|^order)) := by
  filter_upwards [original F Q paid A g L Ln order n p v D m c M η ε Mn ηp ep,
    paid.tested n p J v w m M η ε δ Mn ηp ep dp] with r co obs
  exact fun s z y hz hy=>⟨(obs s z y hz hy).2,co s z hz⟩

end YM.Integration.WilsonCenteredNestedPhysical

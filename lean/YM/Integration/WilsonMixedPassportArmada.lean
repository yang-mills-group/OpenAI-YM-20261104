import YM.Integration.WilsonMixedPassportRows

/-! A restricted, rerouted marked face retains its original rooted price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMixedPassportArmada
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn WilsonMixedPassportRows
open Push Push.AbsoluteSums
open private lengths centered from YM.Integration.WilsonMixedPassportRows
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V ι α β : Type} [DecidableEq V] {C : Census V}
  {P : Passport n V} (M : ι → Row P C G α)
  (face : Finset V) (p : V → Passport n V) (home : ∀ v ∈ face, p v = P)
  (test : β → α)

def roster (i : Face M face) : Row (passport p) C G β :=
  place p (M i.val) (fun v hv => home v (i.property hv)) test

theorem original (w : V → ℝ) (t t' : V → ℕ) {s cost : ℝ} {order arity width : ℕ}
    (input : Scene.Armada M w t s cost order arity width)
    (room : Scene.Ministry C t' arity width) (same : ∀ v ∈ face, t' v = t v) :
    Scene.Armada (roster M face p home test) w t' s cost order arity width := by
  let X := roster M face p home test
  have center (i : Face M face) : (X i).center = (M i.val).center :=
    centered p (M i.val) (fun v hv => home v (i.property hv)) test
  have length (i : Face M face) : (X i).length = (M i.val).length :=
    lengths p (M i.val) (fun v hv => home v (i.property hv)) test
  refine ⟨room, input.positive, ?_, ⟨fun i => input.purchases.spend i.val, ?_⟩, fun i x => input.honor i.val (test x)⟩
  · intro y
    have inv (i : Face M face) :
        (if (X i).center = y then Poly.toll w (X i).mode * (X i).height s else 0) =
          (if (M i.val).center = y then Poly.toll w (M i.val).mode * (M i.val).height s else 0) := by
      unfold Row.height
      rw [center i, length i]
      rfl
    simpa only [← funext inv] using
      (budget_pull (Subtype.val : Face M face → ι) Subtype.val_injective (input.suggests y))
  · intro i
    obtain ⟨he, hsum⟩ := input.purchases.usable i.val
    refine ⟨he, hsum.trans ?_⟩
    exact Finset.sum_congr rfl (fun v hv => (same v (i.property hv)).symm)

end YM.Integration.WilsonMixedPassportArmada

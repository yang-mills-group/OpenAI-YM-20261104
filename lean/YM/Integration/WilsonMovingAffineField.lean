import YM.Integration.WilsonMovingGaussianCoordinates
import YM.MSbar.Rolling.Stove

/-! The actual affine Gaussian integrand of the moving posterior on every
fine link, with its genuine coarse mean, original tree and full free noise. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingAffineField
open Function Lattice Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Next.Free MSbar.Rolling
open scoped Classical Matrix
variable {G : Gauge} {c f : Side} {S : StepData c f}

theorem field (F : Forest S.ratio) (ρ : fieldDir G c 1 → AxisChart G F)
    (b : Positions (Primary c G)) (z : Positions (Key F G)) :
    taps F G *ᵥ (poring F ρ *ᵥ b + straight F G *ᵥ z) =
      Reef.offer G F ((center F ρ b+z) ∘ (Reef.pines F).symm) ∘
        WilsonMovingGaussianCoordinates.link G f := by
  unfold taps poring MSbar.Rolling.straight
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  exact WilsonMovingGaussianCoordinates.stored F (center F ρ b+z)

theorem onRun (R : Run G) (N i per : ℕ) (hi : i<N)
    (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices)
    (b : Positions (Primary (R.family.S.side i per) G)) (z : Positions (Key F G)) :
    let S := R.family.path.levels.clock.op i per
    let K := (RunFormalChain.fromRun R).step N i per hi
    let x := (tint G (Body 1 (R.family.S.side i per))) b
    let Q := Bloch.installed S.ratio ((destination R.family.path.levels N i).duo
      R.family.path.levels.clock.kernel.penalty).A0
    taps F G *ᵥ (poring F (K.b F) *ᵥ b + straight F G *ᵥ z) =
      Reef.offer G F (fun j => (Flat.rawMean G S F Q *ᵥ FreeResolvent.flatten x) j +
        z ((Reef.pines F).symm j)) ∘
        WilsonMovingGaussianCoordinates.link G (R.family.S.side (i+1) per) := by
  intro S K x Q
  have mean : center F (K.b F) b =
      fun j => (Flat.rawMean G S F Q *ᵥ FreeResolvent.flatten x) (Reef.pines F j) :=
    WilsonMovingGaussianCoordinates.onRun R N i per hi F tag b
  rw [field, mean]
  apply congrArg (fun y => Reef.offer G F y ∘
    WilsonMovingGaussianCoordinates.link G (R.family.S.side (i+1) per))
  funext j
  simp [Function.comp_apply]

end YM.Integration.WilsonMovingAffineField
end

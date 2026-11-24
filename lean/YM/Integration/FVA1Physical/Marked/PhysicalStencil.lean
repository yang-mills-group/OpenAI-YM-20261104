import YM.Integration.FVA1Physical.Marked.BareWallet
import YM.Integration.FVA1Physical.Marked.Purchased
import YM.Integration.FVA1Physical.Sources.Round2.ConditionalFields
import YM.Extra.MULTISOURCE_TRAJECTORIES.BirthBounds

/-! Compile every physical bare field into a fixed polynomial in the actual
untwisted square-loop operands of the native marked program. The loops, the
polynomial and its minimum degree are fixed before the period, field, test
coefficients, motion, volume and fine cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Source Extra.Trajectories Next.Foundations Progress.DirectedRecipe RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Qlocal Qlocal.Quipu Qlocal.Quipu.Sonnet Qlocal.Quipu.Lasso
open Extra.Histories
open Pressure Tree
open LocalLTE.Sail MergeProof
open scoped BigOperators Classical

structure SquareStencil (G : Gauge) where
  arity : ℕ
  slot : Fin arity → RG.Slot
  polynomial : Bid.Pose G arity

variable {G : Gauge}
def SquareStencil.read (a : SquareStencil G) {c : Side} (x : Site c) (U : Config G c) : ℂ :=
  Bid.lumin a.polynomial (fun j => Vase.amend G 0 false (travel U x (Wand.squarely (G:=G) (a.slot j)).tour))

theorem square_basis_exists (d : ℕ) (i : ((Labels.frames G).level d).Index) :
    ∃ a : SquareStencil G,
      (∀ j,(a.slot j).stencil ⊆ (localSection G d).stencil) ∧
      Bid.lows a.polynomial (((Labels.frames G).level d).grades i).2 ∧
      ∀ (c : Side) (x : Site c) (u : Config G c),
        (localSection G d).places (Pi.single i 1) x u = a.read x u := by
  obtain ⟨m,S,locality,p,hp,lows⟩ := Next.Foundations.valuation G d i
  refine ⟨⟨m,S,p⟩,locality,lows,?_⟩
  intro c x u
  change (localSection G d).evaluate (Pi.single i 1) (expandAt x u) = _
  rw [hp]
  change Bid.lumin p (fun j => (S j).atSite u x) = _
  exact congrArg (Bid.lumin p) (funext fun j => Work.F02.atSite_curvature (S j) u x)

def squareBasis (G : Gauge) (d : ℕ) (i : ((Labels.frames G).level d).Index) : SquareStencil G :=
  (square_basis_exists d i).choose

theorem square_basis_spec (d : ℕ) (i : ((Labels.frames G).level d).Index) :
    (∀ j,((squareBasis G d i).slot j).stencil ⊆ (localSection G d).stencil) ∧
    Bid.lows (squareBasis G d i).polynomial (((Labels.frames G).level d).grades i).2 ∧
    ∀ (c : Side) (x : Site c) (u : Config G c),
      (localSection G d).places (Pi.single i 1) x u = (squareBasis G d i).read x u :=
  (square_basis_exists d i).choose_spec

/-- Exact nonlinear lattice stencil on every field, in the native loop
coordinates before Taylor expansion, with the actual engineering scale,
source placement, signed motion and complex field coefficients. -/
theorem physical_wavelength {I : Type} (X : Run G) {N n : ℕ}
    (Y : Batch X.family.path N n I) (j : I) (u : Config G (X.family.side N n)) :
    let d := Y.demand j
    let a := (X.family.S.a N:ℂ)^d
    let w := ((Labels.frames G).level d).scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j)
    Y.wavelengths j u = a * Motion.scalar (Y.motion j) (a⁻¹ *
      ∑ i : ((Labels.frames G).level d).Index, w i * (squareBasis G d i).read 0
        (pull (Y.motion j).1 (Y.origin N j) u)) := by
  intro d a w
  let v := pull (Y.motion j).1 (Y.origin N j) u
  change a * Motion.scalar _ (a⁻¹ * (X.family.localSection d).places w 0 v) = _
  rw [places_combined X.family,Finset.sum_apply]
  congr 3
  exact Finset.sum_congr rfl (fun i _ => congrArg (w i * ·) ((square_basis_spec d i).2.2 _ 0 v))

end YM.Integration.FVA1Physical.Marked

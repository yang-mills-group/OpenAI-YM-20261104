import YM.FormalBulk08.Roof.Enroll

/-! The finite conditional which computes one step of the independent formal
one-mark graph. The outer finite sum is over all preimages of the output root.
At a fixed observing period the limit includes every lift of every field slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFormalMarkedCubature

open FormalBulk08
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision Stationary Lotus Shore
open Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {D d j t : ℕ} {F : Frame G d}

/-- The initial column on the finite torus is the Taylor series of the
actual section cylinder, multiplied by its independently prescribed test jet.
The power of the microscopic coupling restores the original field slots. -/
theorem ultraviolet (T : SectionData F) (Dfit : d+1 ≤ D) (paid : Bid.pop T)
    (b : Letter F) (f : Dawn.Studio D) (k : ℕ) (rank : (F.grades (mint F b)).2 ≤ k)
    (n : Side) :
    PowerSeries.X ^ (F.grades (mint F b)).2 * Kemp.banner k (Rial.sectionY T Dfit b f) n =
      PowerSeries.C (MvPolynomial.C (Dawn.notch (pet F b) ((Dawn.paper_fits (pet F b)).trans
        (Nat.le_trans d.le_succ Dfit)) f)) *
        paste (fun x : Jets.Rays (wire G n) =>
          (T.places (copy F (mint F b)) 0 (input G n x)).re) := by
  rw [Rial.sectionY, Kemp.banner_coin, mul_left_comm, Rial.debut T _ k rank n paid]

variable (P : Flight j t) (L : Lodge P.patch) (W : Pot G) (ρ : ChartRatio G)
    (branches : P.patch.Branches K G) (block : 2 ≤ P.L.val)

/-- The independent finite conditional before changing to the output coupling.
Every translated input uses its own affine pullback of the test. -/
def finiteTransfer (Y : Anthem D G) (h l : ℕ) (f : Dawn.Studio D)
    (n : Side) (tag : (primary P.patch K n).Choices) : Pap (wire G n) :=
  PowerSeries.C (MvPolynomial.C (Kemp.aven P.L h)) *
    ∑ x : Site P.L, Reef.tossed P ρ branches L n tag (Mesa.stone W _)
      (Kemp.resite (wrap _ (lift x)) (Kemp.banner l (Y (Dawn.throughW x D block f)) _))

variable (origin : Loc G 1) (Y : Plaza F D) (a : hue G) (H : Hol G)
    (path : Court origin F Y) (vacuum : Story W (pink K.penalty P.wing))
    (ratio : LocalRatio ρ) (Dfit : d < D) (degree : d ≤ j) (order : 4 ≤ t)
    (tags : (n : Side) → (primary P.patch K n).Choices)

local notation "clock" => Roof.epoch a P L K W ρ branches
local notation "nextColumn" => Roof.avenue F ρ a P L branches block W Y
local notation "transferMatrix" => Roof.pTrain F ρ a P L branches block W Y

include H path vacuum ratio Dfit degree order

/-- Coefficientwise recovery of the forward product of the normalized graph
and its transfer matrix. The finite reads include the engineering factor,
the full stationary conditional and every term of the kinetic substitution.
The two free torus parameters distinguish the observing period from the
period going to infinity. -/
theorem periodized (b : Letter F) (f : Dawn.Studio D) (n : Side) (e r : ℕ)
    (v : chain (wire G n) r) :
    Tendsto (fun m : Side => ∑ k ∈ Finset.range (e+1),
      Wine.bill (bookH clock) (bookU clock) e k r *
        (Shore.cores (Shore.tray m n)
          (rancho (finiteTransfer P L W ρ branches block (Y b) d (slots F b) f (m*n) (tags (m*n))) k r) v))
      atTop (𝓝 (rancho (Kemp.banner d ((Roof.larch nextColumn transferMatrix) b f) n) e r v)) := by
  let pre := Kemp.quick P L W (Y b) ρ branches block d d
  have input := (path.officers b).fare
  have admitted : Wade origin pre d :=
    (Kemp.quick_Wade origin P L (Y b) W ρ branches input vacuum ratio block order (slotsFits F b) d).through
      (slotsFits F b)
  have forward := (Roof.axle F ρ a P L branches block W Y path vacuum ratio H Dfit degree order).2
  rw [congrFun forward b]
  change Tendsto _ _ (𝓝 (rancho (Kemp.banner d (Kemp.stir (bookH clock) (bookU clock) pre f) n) e r v))
  rw [Kemp.banner_stain admitted, Wine.stamp_book]
  simp only [Wine.stamp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply tendsto_finsetSum
  intro k _
  apply tendsto_const_nhds.mul
  rw [Kemp.badge (pre f) (admitted.1 f) (admitted.2.1 f) le_rfl]
  obtain ⟨η, eta_pos, estimates, _⟩ := Kemp.brig origin P L (Y b) W ρ branches
    input vacuum ratio block order (slotsFits F b) tags k r d
  have convergence := Kemp.sieve_copy n (estimates f) eta_pos v
  refine convergence.congr' (.of_forall fun m => ?_)
  rw [Kemp.preQ origin P L W ρ branches input block (slotsFits F b) tags f d]
  rfl

end YM.Integration.WilsonFormalMarkedCubature


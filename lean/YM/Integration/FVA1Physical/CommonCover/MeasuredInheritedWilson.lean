import YM.Integration.FVA1Physical.CommonCover.PhysicalInheritedPosterior
import YM.Integration.FVA1Physical.Exchange.ContinuumLimitOriginalForestColumns

/-! Normalize the inherited physical error by the exact receiving vacuum
and center at the actual independent Wilson table used in the forest
comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter Function Finset RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual OriginalMixedWilson
open scoped Classical
variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I}
variable {G : Gauge} (H : History G) (sel : H.Selected) {N n j : ℕ} (step : j<N)
local notation "S" => H.levels.clock.op j n
local notation "fine" => H.rep N n (j+1)
local notation "coarse" => H.rep N n j
local notation "g" => measuredCoupling (H.β N n (j+1))
include sel step

/-- The mask pays its own fraction of one physical vacuum. The input
hypothesis is a bound on the actual inherited activity and marked-log
perturbations. It contains no conclusion about the outgoing step. -/
theorem measured_wilson_older {O : ChartRatio G}
    (K : @Bulk.Kernel G (H.S.side j n) (H.S.side (j+1) n) S (fine).clip (fine).path O)
    (F : Forest (S).ratio) (W : Bulk.Colors R G (H.S.side (j+1) n))
    (D : Lit R (Config G (H.S.side (j+1) n))) (floor : Floor (fine) D)
    (well : Bulk.Well W) (w : I→ℝ) (hw : ∀i,0<w i) (x : fieldDir G (H.S.side j n) 1)
    (r : ℕ) (tag : (S).Choices) (cap : ℝ) :
    let V := sample g x
    let A := zone K (fine).p F g x
    let Q := value (g:ℂ) (ratio (Bulk.Fk K F tag W x r))
    let E := ∑ t:(S).Choices,charge (F.order G) (older K F t g (levelScalar (fine)) x W A D)
    let z := (coarse).eval V
    let k := forestWeight H (N:=N) F V
    let p := (∫y in A,k y ∂F.order G)/z
    (∀y∈A, relativeInlet K g W D w Q (F.drape y)≤cap) →
      0≤p ∧ p≤1 ∧ Poly.price w ((z:ℂ)⁻¹ • (E-E.part R.quiet • Q)) ≤ p*cap := by
  intro V A Q E z k p localFee
  have heat : (fine).beta=temperature g := (physical_temperature H sel (n:=n) step).symm
  have area := plausible K F (fine).p g x
  have zoned : MeasurableSet A := area.1
  have calm : ∀ y∈A,F.drape y∈Calm (fine).p := fun _ h => h.2.1
  have bound := all_tags_older K F g x W D w Q floor well hw heat A zoned calm cap localFee
  have realK : ∀y,0≤k y := forest_weight_nonnegative H sel step F V
  have integrable : Integrable k (F.order G) := (forest_measured_column H sel step F V D floor.vacancy floor.safe).1
  have full : (∫y,k y ∂F.order G)=z :=
    forest_original_volume H sel step F V D floor.vacancy floor.safe floor.gauges
  have zpos : 0<z := SectorNext.Vacuum.strictly H sel N n j step.le V
  have atmost : (∫y in A,k y ∂F.order G)≤z :=
    (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall realK) integrable).trans_eq full
  refine ⟨div_nonneg (integral_nonneg realK) zpos.le,(div_le_one zpos).mpr atmost,?_⟩
  rw [Poly.adapted,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos zpos]
  have tagmass : (fun y:F.Slice G => (S).density (temperature g) (F.drape y) V*(fine).eval (F.drape y))=k := by
    funext y
    rw [←heat]
    rfl
  change Poly.price w (E-E.part R.quiet • Q) ≤
    (∫y in A,(S).density (temperature g) (F.drape y) V*(fine).eval (F.drape y) ∂F.order G)*cap at bound
  rw [show (∫y in A,(S).density (temperature g) (F.drape y) V*(fine).eval (F.drape y) ∂F.order G)=
    ∫y in A,k y ∂F.order G from congrArg (fun f => ∫ y in A,f y ∂F.order G) tagmass] at bound
  apply (mul_le_mul_of_nonneg_left bound (inv_pos.mpr zpos).le).trans_eq
  dsimp only [p,div_eq_mul_inv]
  ring

end YM.Integration.FVA1Physical.OlderPrice

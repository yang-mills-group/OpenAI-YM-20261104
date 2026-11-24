import YM.Integration.NativeRegulatorInitialDatum
import YM.Integration.NativeRegulatorActionStep

/-! Normalized marked and vacuum fields on the first genuine Wilson block,
with the quadratic and cubic kinetic jets on the exact coarse path. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorFirstBlock

open Function Filter Lattice Wilson Precision RG Labels PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal
open PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2
open Integral Exterior Arm Marker Multi Pipeline Pipeline.See Period.Field Sound
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement NativeFormalRegulatorCollector
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalDiagonalCollector PowerSeries
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {hG : G.Simple} {W : Bank R hG} {μ : ℝ}
  {P : MS.Land.Prescription (nativeDeck R)} {Z : branches R}
  {C : Lodge.Contract R (program R) Z} {A : table R} {g : G.ColorIndex}
  {I : Type} [Fintype I] [DecidableEq I] {i : I} {S : Marker.Census I}
  (T : Trial W μ P Z C A g i S)

local notation "𝓑" => C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)
local notation "periodSystem" => Period.Field.LodgeT.instance_real (program R) Z R C
  (schedule Z C T.order) (above Z C T.order)
local notation "𝓛" => Calibration.sheet T.calibrate
local notation "σ" => T.stop T.station

variable {n : ℕ} (v : Pegs.Motor (C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)) n T.station)
  (d : Fin n → ℕ) (u : (a : Fin n) → (R.family.labels.level (d a)).Index)
local notation "𝓐" => T.stamp.traces T.station n σ v d u
local notation "𝓕" => Figure.prop R (ProgramT.spend (program R) Z R C
  (schedule Z C T.order) (above Z C T.order) T.location T.station n v) d u
variable (j : ℕ) (x : fieldDir G (R.family.side (NativeRegulatorInitialDatum.level T j) (T.stop T.station)) 1)
local notation "step₀" => NativeRegulatorInitialDatum.first T j
local notation "Y₁" => (periodSystem).records (𝓑).desk R.family.path σ (step₀).next
local notation "L₁" => T.stamp.menu.cloth (step₀).next
local notation:max "data₀" a:max => NativeRegulatorInitialDatum.datum T v d u j a
open Comparison.RG02.Moving.Path

/-- The native opening unit cost leaves every coefficient of a finite
field-valued display unchanged through the chosen truncation. -/
theorem dormant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Adjacent.Display E) (r k : ℕ) (hk : k ≤ r) (x : E) :
    Adjacent.born F Boot.dormant 0 r k x = F k x := by
  have he : (fun t : ℝ => Adjacent.ages F 0 r t (Boot.dormant.rating t) x) =
      peval (fun j => F j x) r := by
    funext t
    simp [Adjacent.ages, Adjacent.cover, Boot.dormant, peval, Zone.eval, Complex.real_smul]
  exact (congrArg (fun f : ℝ → ℂ => Comparison.RG02.Moving.Path.motion f k) he).trans
    ((Adjacent.polary _ k r).trans (if_pos hk))

private def unit : Adjacent.Caliber := ⟨fun k => if k=0 then 1 else 0,by simp⟩
private theorem even (r : ℕ) : unit.EvenK r := fun k _ hk => if_neg (by intro h; subst k; exact Nat.not_odd_zero hk)

include v j x

/-- Every original first-block outgoing marked field is the literal normalized
local coefficient on its Wilson input and actual adjacent Gaussian kernel. -/
theorem marked (k : ℕ) (hk : k ≤ T.order) :
    See.prime periodSystem S i 𝓛 σ T.order T.stamp.menu 𝓐 (x := (step₀).next) x k =
      LocalFormal.runCoefficients R (data₀ x) T.order k (S.fire i) := by
  rw [NativeRegulatorActionStep.marked T v d u step₀ x hk, show T.stamp.menu.cloth (step₀).prev =
    Boot.dormant from T.stamp.menu.top j]
  exact dormant _ _ _ hk x

/-- The very same first-step vacuum is the centered, unrescaled actual local
vacuum action, for arbitrary spatial directions at each requested order. -/
theorem vacuum (k : ℕ) (hk : k ≤ T.order) :
    See.visible S (Y₁).clip (Y₁).path L₁ (𝓐 (step₀).next) k x =
      (data₀ x).vacuumAction (RunFormalChain.fromRun R) T.order k x -
      (data₀ 0).vacuumAction (RunFormalChain.fromRun R) T.order k 0 := by
  rw [NativeRegulatorActionStep.vacuum T v d u step₀ x hk, show T.stamp.menu.cloth (step₀).prev =
    Boot.dormant from T.stamp.menu.top j]
  let V (a : ℕ) (y : fieldDir G (R.family.side (NativeRegulatorInitialDatum.level T j) σ) 1) :=
    (data₀ y).vacuumAction (RunFormalChain.fromRun R) T.order a y
  exact congrArg₂ (fun a b : ℂ => a-b) (dormant V _ _ hk x) (dormant V _ _ hk 0)

local notation "out₀" => R.family.path.rep (NativeRegulatorInitialDatum.level T j+1) σ (NativeRegulatorInitialDatum.level T j)
local notation "kinetic" => Extra.Iteration.Calibration.main (n := R.family.side (NativeRegulatorInitialDatum.level T j) σ) (out₀).path (out₀).clip

theorem quadratic :
    (data₀ x).vacuumAction (RunFormalChain.fromRun R) T.order 0 x = -(↑(Assembly.jet kinetic 2 x) : ℂ) := by
  have h := (data₀ x).resetVacuumAction_actual_quadratic (RunFormalChain.fromRun R) unit T.order x
  rw [(data₀ x).resetVacuumAction_zero_eq (RunFormalChain.fromRun R) unit T.order,
    NativeRegulatorInitialDatum.cutoff T v d u j x] at h
  exact h

theorem cubic (hr : 1 ≤ T.order) :
    (data₀ x).vacuumAction (RunFormalChain.fromRun R) T.order 1 x = -(↑(Assembly.jet kinetic 3 x) : ℂ) := by
  have hstd : (data₀ x).colors.Standard := by
    rw [NativeRegulatorInitialDatum.colors T v d u j x]
    exact Boot.authentic S i R.family.path (RunFormalChain.fromRun R) _ _ (𝓕 j)
  have h := (data₀ x).resetVacuumAction_actual_cubic (RunFormalChain.fromRun R) unit T.order hr (even _) hstd hG x
  rw [(data₀ x).resetVacuumAction_one_eq (RunFormalChain.fromRun R) unit T.order (even _) hr,
    NativeRegulatorInitialDatum.cutoff T v d u j x] at h
  exact h

theorem outgoing_quadratic :
    See.visible S (Y₁).clip (Y₁).path L₁ (𝓐 (step₀).next) 0 x =
      -(↑(Assembly.jet kinetic 2 x) : ℂ) - (-(↑(Assembly.jet kinetic 2 0) : ℂ)) := by
  exact (vacuum T v d u j x 0 (Nat.zero_le _)).trans
    (congrArg₂ (fun a b : ℂ => a-b) (quadratic T v d u j x) (quadratic T v d u j 0))

theorem outgoing_cubic (hr : 1 ≤ T.order) :
    See.visible S (Y₁).clip (Y₁).path L₁ (𝓐 (step₀).next) 1 x =
      -(↑(Assembly.jet kinetic 3 x) : ℂ) - (-(↑(Assembly.jet kinetic 3 0) : ℂ)) := by
  exact (vacuum T v d u j x 1 hr).trans
    (congrArg₂ (fun a b : ℂ => a-b) (cubic T v d u j x hr) (cubic T v d u j 0 hr))

end YM.Integration.NativeRegulatorFirstBlock
end

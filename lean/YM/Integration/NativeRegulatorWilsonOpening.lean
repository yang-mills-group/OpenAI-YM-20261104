import YM.Integration.NativeFormalDiagonalCollector

/-! The original finite regulator stamp begins with the Wilson action and
the requested mark. Its stopped coefficients are read from the same trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeRegulatorWilsonOpening

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
local notation:max "opening" j:max => Page.opening (𝓑).entire j
local notation:max "N" j:max => (periodSystem).vol (opening j)
local notation:max "D" j:max => R.family.path.rep (N j) σ (N j)

include v

theorem setup : See.Setup (RunFormalChain.fromRun R) periodSystem S i 𝓕 𝓛 σ T.order T.stamp.menu 𝓐 :=
  T.stamp.laws T.station n σ v d u

theorem initial (j : ℕ) : 𝓐 (opening j) = Boot.ink S i R.family.path (N j) σ (𝓕 j) :=
  (setup T v d u).top j

theorem vacuum (j : ℕ) (s : ℝ) (U : Config G (R.family.path.S.side (N j) σ)) :
    (𝓐 (opening j)).vac s U + mainTerm (D j).clip (D j).path U = Wilson.energy U ∧
      Precision.loop (D j).path U = 0 := by
  rw [initial T v d u j]
  exact ⟨sub_add_cancel _ _, Boot.kept0 R.family.path (RunFormalChain.fromRun R) (N j) σ U⟩

theorem marker (j : ℕ) (a : Multi.Hot S) (s : ℝ)
    (U : Config G (R.family.path.S.side (N j) σ)) :
    (𝓐 (opening j)).mark a s U = if a = Arm.pub i then (↑((𝓕 j).Vt _ U) : ℂ) else 0 := by
  rw [initial T v d u j]
  rfl

theorem observed (b : Page (𝓑).entire) (x : fieldDir G (R.family.path.S.side ((periodSystem).vol b) σ) 1)
    {k : ℕ} (hk : k ≤ T.order) :
    See.prime periodSystem S i 𝓛 σ T.order T.stamp.menu 𝓐 (x := b) x k =
      Uniforms.cuff ((observe Z (RunFormalChain.fromRun R) periodSystem 𝓕 𝓛 σ) b) (Kick.depthF Finset.univ d u) k x ∧
    visible S ((periodSystem).records (𝓑).desk R.family.path σ b).clip ((periodSystem).records (𝓑).desk R.family.path σ b).path
        (T.stamp.menu.cloth b) (𝓐 b) k x =
      Uniforms.cloth ((periodSystem).records (𝓑).desk R.family.path σ b).clip ((periodSystem).records (𝓑).desk R.family.path σ b).path
        ((work Z (RunFormalChain.fromRun R) periodSystem 𝓛 σ) b) k x :=
  See.observes (program R) Z (RunFormalChain.fromRun R) periodSystem S i 𝓕 𝓛 σ T.order T.stamp.menu
    (Sound.flatTop (program R) Z T.paid.pillar) (setup T v d u) b x hk

theorem stopped {k : ℕ} (hk : k ≤ T.order) :
    coeff k (ProgramT.Ink (program R) Z R C (schedule Z C T.order) (above Z C T.order)
      T.calibrate T.order T.stop T.location S i T.stamp T.station n v d u) =
      See.prime periodSystem S i 𝓛 σ T.order T.stamp.menu 𝓐 (x := (𝓑).stop.choose T.station) 0 k := by
  change coeff k (Sound.coins periodSystem 𝓛 σ S i T.stamp.menu 𝓐 ((𝓑).stop.choose T.station)) = _
  rw [Sound.coins, coeff_mk, if_pos hk]

end YM.Integration.NativeRegulatorWilsonOpening
end

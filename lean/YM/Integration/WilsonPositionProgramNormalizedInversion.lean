import YM.Integration.WilsonPositionProgramInversionMaterial
import YM.Integration.WilsonPositionProgramReporterBand

/-! A single original inversion tree receives the complete one-source normalized
master at the selected higher cutoff. Its angular coefficients, distinct child
positions, coupling-dependent doses and all ordinary submoments are retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramNormalizedInversion
open Finset Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension
open PhysicalNext.Repeat.Legato Labels Source Precision PertExtension.Orb
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Shard WilsonCoeffUV.Soil WilsonCoeffUV.Power
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonPositionProgramInversionMaterial
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [LinearOrder I]
local notation "L" => R.family.path.levels
variable (d : I → ℕ) (z : I → Cover)
local notation "F" j => R.family.labels.level (d j)
local notation "T₀" j => R.family.localSection (d j)

theorem placed (p : XSpace.Period) (a : Axes R d) (U : Config G p.side) :
    WilsonPositionProgramCopyTop.planted R p d z (axis R d a) U =
      ∏ j, ((T₀ j).places (Pi.single (sheet (F j) (a j)) 1) 0
        (Lattice.translate (wrap p.side (z j)) U)).re := by
  change (∏ j, SlotEvaluation.fieldAt (T₀ j) (sheet (F j) (a j)) (wrap p.side (z j))) U = _
  simp only [Finset.prod_apply,SlotEvaluation.fieldAt,SectionData.places_trans,zero_add]

theorem original (Z : XSpace.Run) (stage : ℕ) (B : WilsonPositionProgramReporterBand.Band R Z stage)
    (t : ℕ) (h : I → ℕ) (fit : ∀ j,d j < h j) (X : (j : I) → Verse (F j))
    (b : (j : I) → Volume (h j)) (D : ChartRatio G) (legal : LocalRatio D)
    (T : (Z.step (B.index t)).p.Tree) :
    let p := (Z.step (B.index t)).p
    let m := B.reporter+t
    let N := m+B.upper t
    let Q := fun j => BayV (primes G) (d j) (h j) (fit j)
    let x := fun j => PermuteLens L R.metals.O (Q j) N m (X j)
    let v := fun j => steep L R.metals.O (T₀ j) (fit j) N m (N-m) (x j)
    let Y := fun j => WilsonCoeffUV.Wheel.Mark.centralL L R.metals.O N m N (Q j) (x j)
    let ζ := dose R d v h fit b
    (∀ j, PowerSeries.X^WilsonPositionProgramMasterBirth.rank R (d:=d j) *
      flash (jot (b j) ((Y j).1 p.side)) =
      ∑ s, PowerSeries.X^(WilsonPositionProgramMasterBirth.rank R (d:=d j)-valence (F j) s) *
        Blue.soil (v j s) * (jewelBloom (fit j) s (b j) • jet (Plies (T₀ j) (sheet (F j) s) p.side))) ∧
    (∀ (a : Axes R d) (U : Config G p.side), WilsonPositionProgramCopyTop.planted R p d z (axis R d a) U =
      ∏ j, ((T₀ j).places (Pi.single (sheet (F j) (a j)) 1) 0
        (Lattice.translate (wrap p.side (z j)) U)).re) ∧
    XSpace.Bare.normalized T G (finite R p d z T ζ) =
       PowerSeries.X^(ceiling R d) * ∑ a, ζ a * reported R p d z D a := by
  intro p m N Q x v Y ζ
  exact ⟨fun j => WilsonPositionProgramMasterBirth.original R (fit j) N m p.side (X j) (b j),
    placed R d z p, WilsonPositionProgramInversionMaterial.original R p d z T D legal ζ⟩

end YM.Integration.WilsonPositionProgramNormalizedInversion
end

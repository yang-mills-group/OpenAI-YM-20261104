import YM.Integration.WilsonMeasuredOwnSiteSource
import YM.Integration.WilsonPositionThermometerGradedReading

/-! The original three named cutoff fields have specific own-site inverse
coordinates on every elected route. Read the complete source and its signed
hard correction at those precise coordinates, without substituting a
separately chosen field or a different normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerNominatedSource
open Function Filter Finset Lattice Wilson RG Source Labels Extra.Histories
open RG.Shoot Marker Overlay Relay PhysicalNext Repeat Legato Graces Roost
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe AllOrder AllOrder.Transit WheelP AllOrder.Floe
open QuadraticLocal.Advent RG05Readout Native Address Many RG05Readout.Records MergeProof Accent
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open RG17 Trace.Pilot Climb Table Spec WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource
open scoped Topology Classical
variable {G:Gauge}

def own (C:Family G) {m N per d:ℕ} (r:Emblems C d) (live:m ≤ N) (z:C.label d) : Palette C d :=
  (finer r live).symm (Pi.single (primaryLetter d) ((C.factory d N per).terminal.symm z))

theorem fired (C:Family G) {m N per d:ℕ} (r:Emblems C d) (live:m ≤ N) (z:C.label d) :
    (C.factory d N per).terminal (finer r live (own C (per:=per) r live z) (primaryLetter d))=z := by
  simp [own]

variable (R:Run G) (A:Group R.family 6) (j:Fin 3)
set_option quotPrecheck false
local notation "d" => (grade j).val
local notation "v" => vector A Finset.univ j

theorem original {start base m N per k:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ u,Rep G (R.family.side u per)) (course:Concourse R.alloy R.kit R.T π Γ start N per k Ψ)
    (since:start ≤ m) {D:Rail R.family} {B:ℕ→ℕ→ℝ} {V:Sight R.family d per}
    {r:Emblems R.family d} (z:Site (R.family.side N per))
    (gauge:Enrolled R.makes D B base N per d (digits R N per z) V r)
    (aged:base ≤ m) (live:m ≤ N) (starts:∀ e ≤ d,R.family.ref e ≤ N) :
    let C:=R.family
    let P:=C.path.rep N per m
    let W:=Ψ m
    let x:=A.station.wheel.atCut (N,per) (index A (grade j)) v
    let y:=own C (per:=per) r live x
    let o:=(C.S.toDepth live per).parent z
    let E:=dyes C m N per live ((C.S.a m:ℂ)^d • C.O N per x z)
    let M:=B d m*size y
    ∃ X Q:Coefficient (C.labels.level d) (C.side m per),
      Trace.Physical.Germ.projection (C.labels.level d) C.params W.p.threshold 0 X=y (primaryLetter d) ∧
      X.Format 0 C.params W ∧ X.remBound 0 W (Push.Local.kappa C.path m) M ∧
      Q.Format o C.params W ∧ Q.remBound o W (Push.Local.kappa C.path m) M ∧
      Q.density o (C.localSection d) P=E ∧ (∀ U,Q.density o (C.localSection d) W U-E U =
        ActualWilsonGraphReclosure.gas W Q U-ActualWilsonGraphReclosure.gas P Q U) ∧
      Q.density o (C.localSection d) W =ᶠ[𝓝 1] E := by
  intro C P W x y o E M
  have h := WilsonMeasuredOwnSiteSource.original R π Γ Ψ course since z gauge aged live starts y
  dsimp only at h
  have fixed : (R.family.factory d N per).terminal (finer r live y (primaryLetter d))=x :=
    fired R.family r live x
  rw [fixed] at h
  exact h

end YM.Integration.WilsonThermometerNominatedSource
end


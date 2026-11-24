import YM.Integration.WilsonMaxwellThermometerPublicStation
import YM.Integration.WilsonPositionThermometerGradedReading
/-! The original station's physical field and the public position regulator:
conversion of every native engineering grade at the same real radius. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPositionCurrency
open Function Set Filter Finset Table Spec Extraction OPE OPE.Orbits Trace Climb
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonPositionThermometerCapStation WilsonMaxwellThermometerPublicStation
open Trace.Pilot Cells RG12 Next.UVStress
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)


/-- Exactly the Wilson observable inserted by the stationed Cap 6/4/4 reading. -/
theorem physical (A:Group R.family 6)(z:ℕ×ℕ)(S:Finset (Fin 3))
    (o:Fin 3→Site (R.family.side z.1 z.2)):
    WilsonPositionThermometerGradedReading.row A z o S=R.family.omega z.1 z.2
      (fun U=>∏i:Fin 3,
        ((R.family.S.a z.1:ℂ)^(WilsonPositionThermometerGradedSource.grade i).val)⁻¹ •
        (R.family.localSection (WilsonPositionThermometerGradedSource.grade i).val).places
          ((R.family.labels.level (WilsonPositionThermometerGradedSource.grade i).val).scaled
            (R.family.path.levels.clock.threshold z.1)⁻¹
            ((R.family.factory (WilsonPositionThermometerGradedSource.grade i).val z.1 z.2).terminal.symm
              (A.station.wheel.atCut z (index A (WilsonPositionThermometerGradedSource.grade i))
                (WilsonPositionThermometerGradedReading.vector A S i)))) (o i) U):=rfl

theorem appointment {r:ℝ} (A:Group R.family 6)(hr:A.station.wheel.r=r):
    R.family.S.a A.station.k*Next.Rank.Station.mag R.family.path.levels A.station.b A.station.k=r:=hr

theorem spacing {r:ℝ} (A:Group R.family 6)(hr:A.station.wheel.r=r):
    R.family.S.a A.station.k/r=(Next.Rank.Station.mag R.family.path.levels A.station.b A.station.k)⁻¹:=by
  rw [←appointment R A hr]
  field_simp [(R.family.S.a_pos _).ne']

variable {n d:ℕ} (W:Initialize G) (X:Sample n) (a:ℝ)

/-- The public regulator reannounces each lower grade at its own metric
width while the submitted physical source has one overall engineering cap. -/
def received (p:Sec G d):Sec G d:=
  ∑j:Fin (d+1), ((X.F.spacing:ℂ)^j.val/(a:ℂ)^d) •
    en (Nat.le_of_lt_succ j.isLt) (Normalize.part d j.val p)

def physicalWord (p:Sec G d)(o:X.F.Sites):Bare.Series (W.tree (grab X).p) G:=
  ((a:ℂ)^d)⁻¹ • ∑j:Fin (d+1),
    On.stencil W.hol (W.surveys j.val) _ _ o (Normalize.part d j.val p)

theorem single (p:Sec G d)(o:X.F.Sites):
    regal W d X o (received X a p)=physicalWord W X a p o:=by
  rw [received,map_sum,physicalWord,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,regals,Initialize.atSite,LinearMap.smul_apply,smul_smul]
  congr 1
  have scale:(X.F.spacing:ℂ)≠0:=Complex.ofReal_ne_zero.mpr X.F.positive.ne'
  field_simp [scale]

theorem ordinary (p:Tags G d n)(S:Finset (Fin n)):
    numberA W d X (fun i=>received X a (p i)) S=
      Bare.normalized _ G (∏i∈S,physicalWord W X a (p i) (chartV X i)):=by
  rw [numberA]
  simp_rw [single]

/-- At the top weight the actual station currency is exactly r^{-d}, on
the actual public chart and for arbitrary original period. -/
theorem top (d:ℕ)(k per:ℕ)(r:ℝ)(hr:0<r):
    let board:=WilsonSeparatedOriginalThermometerDetectorMesh.chart R k per
      (R.family.S.a k/r) (div_pos (R.family.S.a_pos _) hr)
    (board.spacing:ℂ)^d/(R.family.S.a k:ℂ)^d=((r:ℂ)^d)⁻¹:=by
  change ((R.family.S.a k/r:ℝ):ℂ)^d/(R.family.S.a k:ℂ)^d=((r:ℂ)^d)⁻¹
  rw [Complex.ofReal_div,div_pow]
  have h:(R.family.S.a k:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne'
  field_simp [h]

end YM.Integration.WilsonMaxwellThermometerPositionCurrency
end

import YM.Integration.WilsonMaxwellThermometerReflectedMeteredLowerReturn
import YM.Integration.WilsonPositionProgramNormalizedInversion
import YM.Integration.WilsonThermometerPositionTunedCorrection
/-! The original inverse submissions on one genuine Wilson inversion. In the
section change at first order, both the constant and derivative of the filed
dose act on the whole normalized signed Wilson cylinder. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedInverseSection
open Function Finset Lattice Wilson RG XSpace Source Source.Drops Labels Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Shard WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonPositionProgramInversionMaterial (Axes axis ceiling dose reported)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionThermometerCapStation (Group)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels)
open WilsonMaxwellThermometerReflectedStation (Name source)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 2→ℕ)(fit:∀j,levels j<d j)
local notation "Q" => deck (G:=G) levels d fit
local notation "L" => R.family.path.levels

def tender (X:Herit Q)(probe:(j:Fin 2)→Volume (d j))(m top:ℕ):Axes R levels→PowerSeries ℂ:=
  dose R levels (fun j=>steep L R.metals.O ((Q j).ans) ((Q j).path) top m (top-m)
    (PermuteLens L R.metals.O (Q j) top m (X j))) d fit probe

variable (W:Initialize G)(p:XSpace.Period)(z:Fin 2 → Cover)
def word (ζ:Axes R levels→PowerSeries ℂ):PowerSeries ℂ:=
  ∑v,ζ v*WilsonThermometerPositionTunedSlope.finite R levels p z (W.tree p) (axis R levels v)
def surveyed (ζ:Axes R levels→PowerSeries ℂ):PowerSeries ℂ:=
  ∑v,ζ v*WilsonThermometerPositionTunedCorrection.surveyed R W levels p z (W.tree p) (axis R levels v)
def change (v:Axes R levels):PowerSeries ℂ:=
  WilsonThermometerPositionTunedCorrection.residual R W levels p z (W.tree p) (axis R levels v)

theorem reads (ζ:Axes R levels→PowerSeries ℂ):
    Bare.normalized (W.tree p) G (WilsonPositionProgramInversionMaterial.finite R p levels z (W.tree p) ζ)=
      PowerSeries.X^(ceiling R levels)*word R W p z ζ:=by
  rw [WilsonPositionProgramInversionMaterial.original R p levels z (W.tree p) R.metals.O R.alloy.B.ratio]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg (ζ v*·)
  apply PowerSeries.ext
  intro j
  simp only [WilsonPositionProgramInversionMaterial.reported,WilsonThermometerPositionTunedSlope.finite,PowerSeries.coeff_mk]
  exact (WilsonPositionProgramCopyTop.original R p levels z (axis R levels v) R.metals.O
    R.alloy.B.ratio (W.tree p) j).symm

theorem ordinary (ζ:Axes R levels→PowerSeries ℂ):
    word R W p z ζ-surveyed R W p z ζ=∑v,ζ v*change R W p z v:=by
  simp only [word,surveyed,change,←Finset.sum_sub_distrib,←mul_sub,WilsonThermometerPositionTunedCorrection.face]

def rent (ζ:Axes R levels→PowerSeries ℂ)(q:ℕ):ℂ:=
  PowerSeries.coeff q (∑v,ζ v*change R W p z v)
theorem first (ζ:Axes R levels→PowerSeries ℂ):
    rent R W p z ζ 1=∑v,((PowerSeries.coeff 0 (ζ v))*PowerSeries.coeff 1 (change R W p z v)+
      (PowerSeries.coeff 1 (ζ v))*PowerSeries.coeff 0 (change R W p z v)):=by
  simp only [rent,map_sum,PowerSeries.coeff_one_mul,PowerSeries.coeff_zero_eq_constantCoeff]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Each deposited charge comes from the actual independently inverted input,
including the selected Re or Im component of the physical atCut and its unit. -/
theorem original (U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)(t:ℕ)
    (A:Group R.family 6)(a:YM.Axis)(b:XSpace.Normalize.Sec G 6)(N per:ℕ)(n:Name)
    (probe:(j:Fin 2)→Volume (d j)):
    let m:=B.reporter+t
    let p:=(U.step (B.index t)).p
    let X:=source R d fit A a b A.station.k n N per
    let ζ:=tender R d fit X probe m (m+B.upper t)
    (∀q,(PowerSeries.coeff (q+ceiling R levels)
      (Bare.normalized (W.tree p) G (WilsonPositionProgramInversionMaterial.finite R p levels z (W.tree p) ζ)))-
      PowerSeries.coeff q (surveyed R W p z ζ)=rent R W p z ζ q) ∧
      rent R W p z ζ 1=∑v,(PowerSeries.coeff 0 (ζ v)*PowerSeries.coeff 1 (change R W p z v)+
        PowerSeries.coeff 1 (ζ v)*PowerSeries.coeff 0 (change R W p z v)):=by
  intro m p X ζ
  refine ⟨?_,first R W p z ζ⟩
  intro q
  rw [reads R W p z,PowerSeries.coeff_X_pow_mul,← map_sub,ordinary]
  rfl

end YM.Integration.WilsonMaxwellThermometerReflectedInverseSection

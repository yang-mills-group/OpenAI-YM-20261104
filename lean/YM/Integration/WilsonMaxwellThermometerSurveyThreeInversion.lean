import YM.Integration.WilsonMaxwellThermometerReflectedInverseSection
import YM.Integration.WilsonMaxwellThermometerSurveyBirth
/-! The same prepared W-section on the emitted inverse and on the public finite tree, with both coefficient changes charged on their actual sockets. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSurveyThreeInversion
open Function Finset Lattice Wilson RG XSpace Source Source.Drops Labels Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Shard WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonPositionProgramInversionMaterial (Axes axis ceiling dose reported)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalThermometerPalette (levels)
open WilsonMaxwellThermometerReflectedStation (Name source)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ)(fit:∀j,levels j<d j)
local notation "Q" => deck (G:=G) levels d fit
local notation "L" => R.family.path.levels



open RegulatorIR.FVAAlt2
open WilsonMaxwellThermometerSurveyIncome (master chapter)
variable (W:Initialize G)
def tender (X:Herit Q)(probe:(j:Fin 3)→Volume (d j))(m top:ℕ):Axes R levels→PowerSeries ℂ:=
  let E:=fun j=>BayV (master W) (levels j) (d j) (fit j)
  dose R levels (fun j=>steep L R.metals.O ((E j).ans) ((E j).path) top m (top-m)
    (PermuteLens L R.metals.O (E j) top m (X j))) d fit probe

variable (p:XSpace.Period)(z:Fin 3 → Cover)
def surveyed (ζ:Axes R levels→PowerSeries ℂ):PowerSeries ℂ:=
  ∑v,ζ v*WilsonThermometerPositionTunedCorrection.surveyed R W levels p z (W.tree p) (axis R levels v)

def raw (ζ:Axes R levels→PowerSeries ℂ):Bare.Series (W.tree p) G:=
  ∑v,Bare.scalar (W.tree p) (PowerSeries.X^(ceiling R levels-WilsonPositionProgramInversionMaterial.degree R levels v)*ζ v)*
     Taylor.expandTaylor ((W.tree p).basis G) (∏j,WilsonThermometerPositionTunedChange.letter R W p (W.tree p) levels z (axis R levels v) j)

theorem reads (ζ:Axes R levels→PowerSeries ℂ):
    Bare.normalized (W.tree p) G (raw R W p z ζ)=PowerSeries.X^(ceiling R levels)*surveyed R W p z ζ:=by
  rw [raw,map_sum,surveyed,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Bare.normalized_scalar,WilsonThermometerPositionTunedChange.shipped]
  rw [show (PowerSeries.X^(Kick.depthF univ levels (axis R levels v)) : Bare.Series (W.tree p) G)=
     Bare.scalar (W.tree p) (PowerSeries.X^(Kick.depthF univ levels (axis R levels v))) by
       simp only [Bare.scalar,map_pow,PowerSeries.map_X],Bare.normalized_scalar]
  change (PowerSeries.X^(ceiling R levels-WilsonPositionProgramInversionMaterial.degree R levels v)*ζ v)*
    (PowerSeries.X^(WilsonPositionProgramInversionMaterial.degree R levels v)*_)=_
  rw [show ceiling R levels=ceiling R levels-WilsonPositionProgramInversionMaterial.degree R levels v+
      WilsonPositionProgramInversionMaterial.degree R levels v from (Nat.sub_add_cancel
        (WilsonPositionProgramInversionMaterial.rank_le R levels v)).symm,pow_add]
  simp only [Nat.add_sub_cancel,WilsonThermometerPositionTunedCorrection.surveyed]
  ring

end YM.Integration.WilsonMaxwellThermometerSurveyThreeInversion
end

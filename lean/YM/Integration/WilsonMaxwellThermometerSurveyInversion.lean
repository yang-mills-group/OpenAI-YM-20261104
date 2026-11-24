import YM.Integration.WilsonMaxwellThermometerReflectedInverseSection
import YM.Integration.WilsonMaxwellThermometerSurveyBirth
/-! The same prepared W-section on the emitted inverse and on the public finite tree, with both coefficient changes charged on their actual sockets. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSurveyInversion
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


open WilsonMaxwellThermometerReflectedInverseSection (word surveyed change)
open RegulatorIR.FVAAlt2
open WilsonMaxwellThermometerSurveyIncome (master chapter)
variable (W:Initialize G)
def tender (X:Herit Q)(probe:(j:Fin 2)→Volume (d j))(m top:ℕ):Axes R levels→PowerSeries ℂ:=
  let E:=fun j=>BayV (master W) (levels j) (d j) (fit j)
  dose R levels (fun j=>steep L R.metals.O ((E j).ans) ((E j).path) top m (top-m)
    (PermuteLens L R.metals.O (E j) top m (X j))) d fit probe

variable (p:XSpace.Period)(z:Fin 2 → Cover)
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

/-- Separates the real changed cylinder from the change in its own inverse.
Both terms retain the full W tree and its one vacuum. -/
theorem difference (ρ υ:Axes R levels→PowerSeries ℂ) :
    word R W p z ρ-surveyed R W p z υ=
      ∑v,(ρ v*change R W p z v + (ρ v-υ v)*
        WilsonThermometerPositionTunedCorrection.surveyed R W levels p z (W.tree p) (axis R levels v)):=by
  rw [← sub_add_sub_cancel (word R W p z ρ) (surveyed R W p z ρ) (surveyed R W p z υ),
    WilsonMaxwellThermometerReflectedInverseSection.ordinary]
  simp only [surveyed,← Finset.sum_sub_distrib,←Finset.sum_add_distrib,sub_mul]

theorem original (U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)(t:ℕ)
    (A:WilsonPositionThermometerCapStation.Group R.family 6)(a:YM.Axis)(b:XSpace.Normalize.Sec G 6)
    (N per:ℕ)(n:Name)(probe:(j:Fin 2)→Volume (d j)):
    let m:=B.reporter+t
    let top:=m+B.upper t
    let X:=source R d fit A a b A.station.k n N per
    let p:=(U.step (B.index t)).p
    let ρ:=WilsonMaxwellThermometerReflectedInverseSection.tender R d fit X probe m top
    let υ:=tender R d fit W X probe m top
    (∀j,let E:=BayV (master W) (levels j) (d j) (fit j)
        let x:=PermuteLens L R.metals.O E top m (X j)
        let v:=steep L R.metals.O E.ans E.path top m (top-m) x
        let Y:=WilsonCoeffUV.Wheel.Mark.centralL L R.metals.O top m top E x
        PowerSeries.X^(WilsonPositionProgramMasterBirth.rank R (d:=levels j))*
          flash (jot (probe j) (Y.1 p.side))=
        ∑s,PowerSeries.X^(WilsonPositionProgramMasterBirth.rank R (d:=levels j)-valence E.F s)*
          Blue.soil (v s)*(jewelBloom E.path s (probe j) • jet (Plies E.ans (sheet E.F s) p.side))) ∧
    ∀q,PowerSeries.coeff (q+ceiling R levels) (Bare.normalized (W.tree p) G
      (WilsonPositionProgramInversionMaterial.finite R p levels z (W.tree p) ρ))-
      PowerSeries.coeff (q+ceiling R levels) (Bare.normalized (W.tree p) G (raw R W p z υ))=
      PowerSeries.coeff q (∑v,(ρ v*change R W p z v + (ρ v-υ v)*
        WilsonThermometerPositionTunedCorrection.surveyed R W levels p z (W.tree p) (axis R levels v))):=by
  intro m top X p ρ υ
  refine ⟨fun j=>WilsonMaxwellThermometerSurveyBirth.original R W (fit j) top m p.side (X j) (probe j),?_⟩
  intro q
  rw [WilsonMaxwellThermometerReflectedInverseSection.reads,reads,
    PowerSeries.coeff_X_pow_mul,PowerSeries.coeff_X_pow_mul,←map_sub,difference]

end YM.Integration.WilsonMaxwellThermometerSurveyInversion
end

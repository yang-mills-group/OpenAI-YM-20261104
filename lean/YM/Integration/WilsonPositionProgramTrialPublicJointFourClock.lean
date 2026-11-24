import YM.Integration.WilsonPositionProgramTrialFittedLens
import YM.FormalBulk08.Series.Level

/-! Coefficient zero on the original returned field and its native clock. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourClock
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Carp
open scoped BigOperators Classical
open PowerSeries

theorem reel (B f:Cost):coeff 0 (Bank.reel B f)=coeff 0 f:=by
  rw [Bank.reel_apply]
  have zero:coeff 0 (B*PowerSeries.X)=0:=by simp [coeff_zero_eq_constantCoeff_apply]
  simpa using YM.FormalBulk08.Series.subst_coeff zero f 0 0 (by decide)

theorem filed {G:Gauge}{d D:ℕ}{F:Frame G d}(A:Levels G)(O:ChartRatio G)
    (T:SectionData F)(p:d<D)(N m k:ℕ)(c:Verse F)(i:Alma F):
    coeff 0 (street A O T p N m k c i)=
      (lineS (CurNames A O T p N m k false) 0 *ᵥ fun a=>coeff 0 (c a)) i:=by
  have mul (f g:Cost):coeff 0 (f*g)=coeff 0 f*coeff 0 g:=by
    simp [coeff_zero_eq_constantCoeff_apply]
  change coeff 0 (∑a, CurNames A O T p N m k false i a*Bank.reel (relativeF A O N m k) (c a))=_
  simp only [map_sum,mul,reel,Matrix.mulVec,dotProduct,lineS,Matrix.of_apply]

theorem measured {G:Gauge}(A:Levels G)(O:ChartRatio G)(Q:SealR G)(N m:ℕ)
    (b:Q.Rider)(i:Alma Q.F):
    coeff 0 (PermuteLens A O Q N m b i)=
      ((Wray A O Q.ans Q.path N m)⁻¹ *ᵥ fun j=>coeff 0 (b j)) i:=by
  simp [PermuteLens,Matrix.mulVec,dotProduct]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourClock

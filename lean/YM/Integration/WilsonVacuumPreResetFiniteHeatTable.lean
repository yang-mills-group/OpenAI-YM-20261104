import YM.Integration.WilsonVacuumPreResetFiniteHeatScale
import YM.WilsonCoeffUV.Reclosure.Paths.RetainBase

/-! The retained positive slots determine the whole genuine finite signed
vacuum comparison, including the empty slot and the unretained ranks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatTable
open Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel WilsonCoeffUV.Blue WilsonCoeffUV.Mer PhysicalNext.Repeat.Legato
open Next.Foundations
variable {G : Gauge}

def table (L:Levels G)(O:ChartRatio G)(e N m:ℕ)(n:Side)(η:ℝ):Prop:=
  ∀a≤e,∀r x,|(story L O N m).1 n a r x-emera (actionW L O N m) n a r x|≤η

theorem top (R:Run G)(e N:ℕ)(n:Side){η:ℝ}(hη:0≤η):
    table R.family.path.levels R.metals.O e N N n η:=by
  intro a _ r x
  change |(story R.family.path.levels R.metals.O N N).1 n a r x-
    emera (story R.family.path.levels R.metals.O N N).2 n a r x|≤η
  rw [story_top]
  cases r with
  | zero => simpa [tale,topW,emera,lop] using hη
  | succ l =>
    have eq:=congrFun (moon_wrap G a l n) x
    simpa only [tale,topW,emera,lop,if_neg (Nat.succ_ne_zero l), eq, sub_self, abs_zero] using hη

theorem all (R:Run G)(simple:G.Simple)(e N m:ℕ)(hm:m≤N)(n:Side){η:ℝ}(hη:0≤η)
    (paid:∀a≤e,∀r,r+1≤a+2→∀x,
      |(story R.family.path.levels R.metals.O N m).1 n a (r+1) x-
        emera (actionW R.family.path.levels R.metals.O N m) n a (r+1) x|≤η):
    table R.family.path.levels R.metals.O e N m n η:=by
  have unwrapped:=(old R.family.path.levels R.metals.O simple R.alloy.B.ratio N m hm).basis n
  have wrapped:=(emera_far R.family.path.levels simple R.alloy.B.ratio hm n).1
  intro a ha r x
  cases r with
  | zero =>
    have eq:=congrFun (congrFun (congrFun unwrapped.clear a) 0) x
    change (0:ℝ)=(story R.family.path.levels R.metals.O N m).1 n a 0 x at eq
    change |(story R.family.path.levels R.metals.O N m).1 n a 0 x-0|≤η
    rw [←eq];simpa using hη
  | succ r =>
    by_cases hr:r+1≤a+2
    · exact paid a ha r hr x
    · rw [unwrapped.lamp a (r+1) (by omega),wrapped a (r+1) (by omega)]
      simpa using hη

end YM.Integration.WilsonVacuumPreResetFiniteHeatTable

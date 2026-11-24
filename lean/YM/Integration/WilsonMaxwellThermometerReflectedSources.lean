import YM.Integration.WilsonMaxwellThermometerIndependentReflection
import YM.Integration.WilsonNeutralCopiedField

/-! The original signed sources in the independent reflected experiment.
The two energy channels use their own cap, the upper uses its complete
enrolled section, and deleting a slot reinstates the true original unit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedSources
open Lattice Wilson Labels PhysicalNext.Repeat.Legato RG Source WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel.Mark WilsonMaxwellThermometerIndependentReflection
open WilsonCoeffUV.Shard WilsonCoeffUV.Blue XSpace XSpace.Normalize Maxwell
open WilsonMaxwellThermometerPublicReflection (energy)
open WilsonNeutralCopiedField (point)
open scoped Classical BigOperators
variable {G:Gauge}

def part (bit:Bool)(c:ℂ):ℝ:=if bit then c.im else c.re
def symbol {h:ℕ}(F:Frame G h)(x:Sec G h)(bit:Bool):Verse F:=
  fun j=> if j=point F (sheet F j) then
    PowerSeries.C (part bit (F.coords (On.sectionMap h x) (sheet F j))) else 0

theorem coefficient {h:ℕ}(F:Frame G h)(x:Sec G h)(bit:Bool)(i:F.Index)(t:ℕ):
    PowerSeries.coeff t (symbol F x bit (point F i))=
      if t=0 then part bit (F.coords (On.sectionMap h x) i) else 0:=by
  change PowerSeries.coeff t (if point F i=point F i then
    PowerSeries.C (part bit (F.coords (On.sectionMap h x) i)) else 0)=_
  simp [PowerSeries.coeff_C]

def omitted {h:ℕ}(F:Frame G h):Verse F:=fun j=>if j=point F 0 then 1 else 0

theorem vacuum (R:Run G)(h:ℕ){n:Side}(o:Site n)(U:Config G n):
    ((primes G).T h).places ((primes G).F h).e0 o U=1:=
  congrFun ((R.makes.sections h).unit) (expandAt o U)

theorem scalar {h:ℕ}(F:Frame G h)(i:F.Index):
    PowerSeries.coeff 0 (omitted F (point F i))=(F.e0 i).re:=by
  by_cases h:i=0
  · subst i; simp [omitted,Frame.e0]
  · have distinct:point F i≠point F 0:=fun eq=>h (congrArg (sheet F) eq)
    simp [omitted,distinct,Frame.e0,Pi.single_eq_of_ne h]

def lower (a:Axis)(s:Bool):Sec G 4:=ori (Signed.reflect a) 4 (reel 4 (energy G s))

def fields {l d:ℕ}(h4:4<l)(h6:6<d)(a:Axis)(b:Sec G 6)(s:Bool)(bits:Fin 2→Bool):
    Herit (panel (G:=G) h4 h6):=
  Fin.cases (motive:=fun i=>(panel (G:=G) h4 h6 i).Rider)
    (symbol ((primes G).F 4) (lower a s) (bits 0)) (fun j=>by
      have eq:j=0:=Subsingleton.elim _ _
      subst j
      exact symbol ((primes G).F 6) b (bits 1))

def units {l d:ℕ}(h4:4<l)(h6:6<d):Herit (panel (G:=G) h4 h6):=
  fun i=>omitted ((panel h4 h6 i).F)

def signs (bits:Fin 2→Bool):ℂ:=∏i,if bits i then Complex.I else 1

theorem price (bits:Fin 2→Bool):‖signs bits‖=1:=by
  rw [signs,norm_prod]
  exact Finset.prod_eq_one fun i _=>by split <;> simp

theorem restored (x y:ℂ):
    ∑bits:Fin 2→Bool,signs bits*((part (bits 0) x:ℝ):ℂ)*(part (bits 1) y:ℝ)=x*y:=by
  classical
  let factors (i:Fin 2)(j:Bool):ℂ:=(if j then Complex.I else 1)*
    (((part j (![x,y] i)):ℝ):ℂ)
  calc
    _=∑bits:Fin 2→Bool,∏i,factors i (bits i):=by
      apply Finset.sum_congr rfl; intro f _
      simp only [signs,Fin.prod_univ_two,factors,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    _=∏i:Fin 2,∑j:Bool,factors i j:=by rw [Fintype.prod_sum]
    _=x*y:=by
      rw [Fin.prod_univ_two]
      simp only [Fintype.sum_bool,factors,part,Bool.false_eq_true,if_false,if_true,
        Matrix.cons_val_zero,Matrix.cons_val_one,one_mul]
      apply congr_arg₂ (·*·) <;> apply Complex.ext <;> simp

end YM.Integration.WilsonMaxwellThermometerReflectedSources

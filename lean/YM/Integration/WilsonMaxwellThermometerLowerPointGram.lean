import YM.Integration.WilsonMaxwellThermometerPublicReflection
import YM.Next.MAXWELL.Core

/-! A reflected two-point detector for the occupied chiral energy span.
The Wilson gauge and the subtraction on both proper faces are fixed before
choosing a lower mixing coefficient. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerLowerPointGram
open Function Set Wilson Maxwell Maxwell.Free WilsonMaxwellThermometerPublicReflection
open scoped Classical BigOperators ComplexOrder
variable {G:Gauge}(a:Axis)(x:E4)

def centeredEnergy (G:Gauge)(a:Axis)(x:E4)(s:Bool):WickPol G :=
  let P := (energy G s).val
  P-star (score a x P 1) • (1:WickPol G)

def occupied (G:Gauge)(a:Axis)(x:E4):Submodule ℂ (WickPol G):=
  Submodule.span ℂ (Set.range (centeredEnergy G a x))

def read (s:Bool)(P:WickPol G):ℂ:=
  score a x ((energy G s).val) P -
    score a x ((energy G s).val) 1 * score a x 1 P

theorem centered (s:Bool)(P:WickPol G):
    read a x s P=score a x (centeredEnergy G a x s) P:=by
  simp only [read,centeredEnergy,sub_eq_add_neg,←neg_smul,score_add,score_scale,star_neg,
    star_star,neg_mul]

def panel (G:Gauge)(a:Axis)(x:E4):occupied G a x →ₗ[ℂ] (Bool→ℂ) :=
  LinearMap.pi fun s=>
    {toFun:=fun v=>score a x (centeredEnergy G a x s) v.val,
     map_add':=fun v w=>score_extend a x _ v.val w.val,
     map_smul':=fun c v=>score_rescale a x _ v.val c}

theorem reported (z:occupied G a x)(s:Bool):
    (panel G a x z) s=read a x s z.val:=(centered a x s z.val).symm

theorem faithful (hx:0<x a):(panel G a x).ker=⊥:=by
  apply le_antisymm _ bot_le
  intro z hz
  have h:=LinearMap.mem_ker.mp hz
  have vanishes:∀w∈occupied G a x,score a x w z.val=0:=by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨s,rfl⟩:=hu
      exact congrFun h s
    | zero =>
      simpa only [zero_smul,star_zero,zero_mul] using
        score_scale a x (0:WickPol G) z.val (0:ℂ)
    | add u v _ _ hu hv => rw [score_add,hu,hv,zero_add]
    | smul c u _ hu => rw [score_scale,hu,mul_zero]
  have equal:=vanishes z.val z.property
  have hi:z.val=0:=by
    by_contra hn
    exact (ne_of_gt (detects a x hx z.val hn)) equal
  have zz:z=0:=Subtype.ext hi
  rw [zz]
  exact Submodule.zero_mem _

/-- Any fixed numerical chart of the true centered occupied space is paid
by the two original reflected moment readings. -/
theorem original {B:Type*}[NormedAddCommGroup B][NormedSpace ℂ B]
    (hx:0<x a)(T:occupied G a x→ₗ[ℂ] B):
    ∃C:ℝ,0≤C ∧ ∀z:occupied G a x,
      ‖T z‖≤C*‖fun s:Bool=>read a x s z.val‖:=by
  obtain ⟨inv,left⟩:=(panel G a x).exists_leftInverse_of_injective (faithful a x hx)
  let D := (T.comp inv).toContinuousLinearMap
  refine ⟨‖D‖,norm_nonneg _,?_⟩
  intro z
  have law:inv (panel G a x z)=z:=LinearMap.congr_fun left z
  have output:D (panel G a x z)=T z:=congrArg T law
  have rows:panel G a x z = fun s=>read a x s z.val:=funext (reported a x z)
  rw [←output,←rows]
  exact D.le_opNorm _

end YM.Integration.WilsonMaxwellThermometerLowerPointGram

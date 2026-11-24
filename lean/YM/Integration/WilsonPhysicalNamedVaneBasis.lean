import YM.Integration.WilsonPhysicalVaneBasis
import YM.Integration.WilsonOriginalPublicRelativeGramFreePanel

/-! The true signed public Maxwell axes in the original weak Vane retain both their weight and their field count. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalNamedVaneBasis
open Filter Function Labels Maxwell Maxwell.Free Maxwell.Wick MS MS.Menus MS.Land MS.Theater
open Lattice Wilson RG Source Cells Further.CorrectedLift PhysicalNext.Repeat.Legato
open Local.Physical XSpace XSpace.Normalize XSpace.Structure1
open Push.CutoffProjectors
open WilsonOriginalPublicRelativeGramFreePanel (named)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(B:Deck G){d:ℕ}(i:Glyph B d)
local notation "C" => R.family
local notation "F₀" => R.family.labels.level d

def filmLabel:Label G d:=
  Labels.raiseLabel G (Nat.le_of_lt_succ i.1.isLt)
    ⟨ΕData B i,limitH (filmBasic B i).2,((cinema (ΕData B i)).mp (filmBasic B i)).2.1⟩

theorem homogeneous:filmLabel B i∈Labels.Grade (i.1.val,i.2.1.val):=
  (nodeId _ _).mp (filmBasic B i).2

theorem names:(Cells.standard C).project d ((F₀).coords (filmLabel B i))=named R B d i:=by
  apply (Maxwell.Free.fields R.family.labels d).injective
  rw [Maxwell.Free.fields_eval,named,Module.Basis.map_apply,LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change (observable G d ((F₀).coords.symm ((F₀).coords (filmLabel B i))))=_ 
  rw [LinearEquiv.symm_apply_apply,readHeight]
  rfl

private theorem power_of_mem {z:ℂ}{m n:ℕ}(active:z≠0)
    (test:Complex.ofReal ((2:ℝ)^m)*z=Complex.ofReal ((2:ℝ)^n)*z):m=n:=by
  have same:Complex.ofReal ((2:ℝ)^m)=Complex.ofReal ((2:ℝ)^n):=mul_right_cancel₀ active test
  exact pow_right_injective₀ (a:=(2:ℝ)) (by norm_num) (by norm_num) (Complex.ofReal_injective same)

theorem original (j:(F₀).Index)(present:(ladder C d (named R B d i)) j≠0):
    (F₀).grades j=(i.1.val,i.2.1.val):=by
  let F:=F₀
  let k:ℕ×ℕ:=(i.1.val,i.2.1.val)
  let z:=F.coords (filmLabel B i)
  let kept:=retain F ((Cells.standard C).null d)
  have pure:∀t,z t≠0 → F.grades t=k:=by
    intro t live
    by_contra wrong
    exact live (F.power_coefficient t (Ne.symm wrong) (homogeneous B i))
  have diag (a:ℕ×ℕ→ℕ):
      (fun j=>Complex.ofReal ((2:ℝ)^a (F.grades j))*z j)=Complex.ofReal ((2:ℝ)^a k) • z:=by
    funext j
    change _=Complex.ofReal ((2:ℝ)^a k)*z j
    by_cases live:z j=0
    · rw [live,mul_zero,mul_zero]
    · rw [pure j live]
  have ht:zoom F 2 (kept z)=Complex.ofReal ((2:ℝ)^k.1) • kept z:=by
    calc
      _=kept (zoom F 2 z):=(free_zoom C 2 z).symm
      _=kept (Complex.ofReal ((2:ℝ)^k.1) • z):=congrArg kept (diag Prod.fst)
      _=_:=map_smul _ _ _
  have hc:F.scaled 2 (kept z)=Complex.ofReal ((2:ℝ)^k.2) • kept z:=by
    calc
      _=kept (F.scaled 2 z):=(free_scaled C 2 z).symm
      _=kept (Complex.ofReal ((2:ℝ)^k.2) • z):=congrArg kept (diag Prod.snd)
      _=_:=map_smul _ _ _
  rw [←names R B i] at present
  change (kept z) j≠0 at present
  exact Prod.ext (power_of_mem present (congrFun ht j)) (power_of_mem present (congrFun hc j))

end YM.Integration.WilsonPhysicalNamedVaneBasis

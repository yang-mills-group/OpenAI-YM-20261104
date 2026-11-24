import YM.Integration.WilsonOriginalPublicRelativeGramRank
import YM.Integration.WilsonViewerGridReflection
import YM.Integration.WilsonPositionPrescribedScreen

/-! Use the physical Maxwell identification on the complete public horizon.
The adjoint leg is first in the true panel and second in the printed Wick Gram. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramFreePanel
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical Extra Extra.FD
open WilsonPositionProgramPublicWickGram (reading nodes vertex)
open WilsonOriginalPublicRelativeGramLeading (fields free)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G)(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)
local notation "E" => Theater.Daylight B h

def named:Module.Basis (Glyph B h) ℂ ((Spin.comparator R.family.book).Field h):=
  (Theater.Daylight B h).map (Maxwell.Free.fields R.family.labels h).symm

private theorem reality (i:Glyph B h):reel h (E i)=E i:=by
  apply Subtype.ext
  change Free.realForm (E i).val=(E i).val
  rw [readHeight]
  exact real_shell B i

theorem adjoint (i:Glyph B h):
    (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) h a (named R B h i)=
      (Maxwell.Free.fields R.family.labels h).symm (τ (Signed.mirror a) h (E i)):=by
  apply (Maxwell.Free.fields R.family.labels h).injective
  rw [← show _=(Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) h a (named R B h i) from
    (rfl:WilsonViewerGridReflection.reflect (R:=R) h a (named R B h i)=_)]
  rw [WilsonViewerGridReflection.free]
  simp only [named,Module.Basis.map_apply,LinearEquiv.apply_symm_apply,reality]

def pointsAt:Points 2:=FD.couple (-(vertex a)) (vertex a)

private theorem mirrorPair (v x:Sec G h):
    scene (pointsAt a) h ![v,x]=scene (nodes a) h ![x,v]:=by
  rw [Normalize.screen,Normalize.screen]
  let swap:=Equiv.swap (0:Fin 2) 1
  have pos:vertex a≠-(vertex a):=by
    intro eq
    have bad:=congrArg norm ((WilsonPositionProgramPublicWickGram.apart a).symm.trans (sub_eq_zero.mpr eq))
    simp [basis_norm] at bad
  have good:=FD.couple_ok (Ne.symm pos)
  have turn:=Maxwell.Wick.exchangeSites (G:=G) swap good (fun i=>(![v,x] i).val)
  have address:points ((FD.couple (-(vertex a)) (vertex a)).ofLp ∘ swap)=nodes a:=by
    apply congrArg points
    funext k
    fin_cases k <;> simp [swap,FD.couple]
  have sides:(fun i=>(![v,x] i).val) ∘ swap=(fun i=>(![x,v] i).val):=by
    funext k
    fin_cases k <;> simp [swap]
  rw [address,sides] at turn
  exact turn

theorem incidence (i j:Glyph B h):
    PhysMS.WickGoal (C:=R.family) (fields R a (fun _:Glyph B h=>h) (fun k=>named R B h k) i j) (pointsAt a)=
      reading a (nodes a) (id:Glyph B h→Glyph B h) i j:=by
  let T:Fin 2→Sec G h:=![τ (Signed.mirror a) h (E i),E j]
  let v:=fields R a (fun _:Glyph B h=>h) (fun k=>named R B h k) i j
  let raw (k:Fin 2):(Bel R.family.book).Tag:=⟨WilsonOriginalBlissMixedGram.grades h h k,v k⟩
  let canon (k:Fin 2):(Bel R.family.book).Tag:=⟨h,(Maxwell.Free.fields R.family.labels h).symm (T k)⟩
  have eq:raw=canon:=by
    funext k
    fin_cases k
    · change (⟨h, (Bel R.family.book).adj _ h a (named R B h i)⟩:(Bel R.family.book).Tag)=⟨h,_⟩
      rw [adjoint R B h a i]
      rfl
    · rfl
  change (Bel R.family.book).useAt (Bel R.family.book) (pointsAt a) raw=_
  rw [eq]
  change PhysMS.WickGoal (C:=R.family) (d:=fun _:Fin 2=>h)
    (fun k=>(Maxwell.Free.fields R.family.labels h).symm (T k)) (pointsAt a)=_
  rw [WilsonPositionPrescribedScreen.zero]
  exact mirrorPair h a (τ (Signed.mirror a) h (E i)) (E j)

end YM.Integration.WilsonOriginalPublicRelativeGramFreePanel

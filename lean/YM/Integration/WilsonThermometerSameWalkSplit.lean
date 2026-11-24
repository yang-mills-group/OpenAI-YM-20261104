import YM.Trace.Physicalv2.Germ
import YM.Extra.SOURCE_HISTORIES.Unit

/-! Split the genuine enrolled coefficient without moving a single regular or
forced address. The part left for the original null gate has zero true germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkSplit
open Function Filter Lattice Wilson Labels RG Source RG.Shoot
open Extra.Histories Trace.Physical.Germ
open scoped Classical Topology BigOperators
variable {G:Gauge} {d:ℕ} {n:Side} {F:Frame G d}
variable (A:Hol G) (S:SectionData F) (P:Rep G n) (o:Site n)

def remove (q:Coefficient F n) (u:F.Coeff):Coefficient F n:={q with x:=q.x-u}

theorem original (q:Coefficient F n) (u:F.Coeff) {κ r:ℝ}
    (shape:q.Format o A P) (paid:q.remBound o P κ r):
    (remove q u).Format o A P ∧ (remove q u).remBound o P κ r ∧
    (remove q u).regular=q.regular ∧ (remove q u).forced=q.forced ∧
    projection F A P.p.threshold o (remove q u)=projection F A P.p.threshold o q-u ∧
    ∀ U, q.density o S P U=(remove q u).density o S P U+(primary o u).density o S P U:=by
  refine ⟨⟨shape.smooth,shape.origin,shape.identity_null,shape.projects,shape.forcing,shape.carried,shape.invariant,shape.supported,shape.borel⟩,paid,rfl,rfl,?_,?_⟩
  · unfold projection
    change q.x-u+_ = (q.x+_)-u
    abel
  · intro U
    rw [primary_density]
    let g:ℂ:=∑'j,q.maskedTerm P j U
    let hard:ℂ:=(Real.exp (P.exponent U):ℂ)*∑'a,q.marked P a U
    change (P.eval U:ℂ)*(part S o P U q.x+g)+hard=
      (P.eval U:ℂ)*(part S o P U (q.x-u)+g)+hard+(P.eval U:ℂ)*part S o P U u
    rw [map_sub]
    ring

theorem measured (q:Coefficient F n) {κ r:ℝ} (shape:q.Format o A P) (paid:q.remBound o P κ r):
    let u:=projection F A P.p.threshold o q
    (remove q u).Format o A P ∧ (remove q u).remBound o P κ r ∧
    projection F A P.p.threshold o (remove q u)=0 ∧ ∀ U,
      q.density o S P U=(remove q u).density o S P U+(primary o u).density o S P U:=by
  intro u
  obtain ⟨hs,hp,_,_,eq,heard⟩:=original A S P o q u shape paid
  exact ⟨hs,hp,eq.trans (sub_self u),heard⟩

theorem unit (u:F.Coeff) (U:Config G n):
    (primary o u).density o S P U=(primary o (F.core u)).density o S P U+(u 0:ℂ)*(P.eval U:ℂ):=by
  have id:=congrFun (unit_density S P o) U
  rw [primary_density] at id
  rw [primary_density,primary_density]
  nth_rw 1 [←Size.core_plus F u]
  rw [map_add,map_smul,smul_eq_mul]
  linear_combination (u 0)*id

end YM.Integration.WilsonThermometerSameWalkSplit
end

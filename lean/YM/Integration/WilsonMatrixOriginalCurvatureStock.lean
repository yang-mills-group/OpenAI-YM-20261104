import YM.Integration.WilsonMatrixOriginalIndependentCentering
import YM.Integration.WilsonReportingPrescribedOldFreeArms

/-! Exact support of the observed engineering horizon and its original two-curvature coefficient table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalCurvatureStock
open Lattice Wilson RG Precision Source Labels Maxwell StressFlux MS.Local.Physical MS.Menus MS.Theater
open UVNext.FreeStress FVA2 FVA2.Warehouse Finset
open WilsonMatrixOriginalIndependentColumns WilsonReportingPrescribedOldFreeArms
open private tape_degree from YM.Integration.WilsonReportingPrescribedOldAction
open scoped Classical BigOperators

variable {G:Gauge} (B:Deck G)

theorem support (simple:G.Simple) (i:Glyph B 4):
    (i.size,i.grade)=(0,0) ∨ (i.size,i.grade)=(4,2):=by
  by_contra no
  push Not at no
  let p:=field B 4 i
  have hp:p ∈ Labels.Grade (i.size,i.grade):=(filmW (h:=i.1.val) B i.2.2).2
  obtain ⟨c,v,parts⟩:=span_four simple p
  have hb (a b:Place 0):Labels.gradePart (i.size,i.grade) (bond (G:=G) a b (d:=4) le_rfl)=0:=
    Labels.gradePart_zero _ (i.size,i.grade) (4,2) no.2 (tape_degree a b)
  have hu:Labels.gradePart (i.size,i.grade) (Labels.unit G 4)=0:=
    Labels.gradePart_zero _ _ (0,0) no.1 (Labels.unit_grade (G:=G) 4)
  have removed:=congrArg (Labels.gradePart (G:=G) (d:=4) (i.size,i.grade)) parts
  simp only [Labels.gradePart_self p _ hp,map_add,map_sum,map_smul,hb,hu,smul_zero,
    Finset.sum_const_zero,zero_add] at removed
  have film_zero:film B i.2.2 (h:=i.1.val)=0:=congrArg (fun u:Labels.Label G 4=>u.val) removed
  have raw_zero:B.raw (i.1.val:ℤ) i.2.1.val i.2.2=0:=by rw [←lamp_here (h:=i.1.val) B i.2.2,film_zero,map_zero]
  exact (Module.finBasis ℝ (B.carries (i.1.val:ℤ) i.2.1.val)).ne_zero i.2.2 (Subtype.ext raw_zero)

def curvature (i:B.BIndex (4:ℤ) 2):Glyph B 4:=⟨⟨4,by decide⟩,⟨2,by decide⟩,i⟩

private theorem injective:Function.Injective (curvature B):=by
  intro i j h
  simpa only [curvature,Sigma.mk.injEq,heq_eq_eq,true_and] using h

private theorem hit (i:Glyph B 4) (h:(i.size,i.grade)=(4,2)):
    ∃j,curvature B j=i:=by
  rcases i with ⟨⟨d,hd⟩,⟨k,hk⟩,i⟩
  change (d,k)=(4,2) at h
  have dn:=congrArg Prod.fst h
  have kn:=congrArg Prod.snd h
  change d=4 at dn
  change k=2 at kn
  subst d;subst k
  exact ⟨i,rfl⟩

/-- A complete finite response vanishing on the lower scalar is precisely the actual curvature array. -/
theorem sum {A:Type*} [AddCommMonoid A] (simple:G.Simple) (f:Glyph B 4→A)
    (unit:∀i,i.size<4→f i=0):
    (∑i,f i)=∑j:B.BIndex (4:ℤ) 2,f (curvature B j):=by
  calc
    (∑i,f i)=∑i∈univ.image (curvature B),f i:=by
      symm
      apply sum_subset (subset_univ _)
      intro i _ absent
      rcases support B simple i with low|top
      · apply unit i
        have z:=congrArg Prod.fst low
        change i.size=0 at z
        omega
      · obtain ⟨j,rfl⟩:=hit B i top
        exact (absent (mem_image_of_mem _ (mem_univ j))).elim
    _=∑j:B.BIndex (4:ℤ) 2,f (curvature B j):=sum_image (fun _ _ _ _ h=>injective B h)

/-- The actually measured curvature coordinates as genuine Stock, with the irrelevant additive
constant set to zero at the point where connected centering erases it. -/
def stock (a:Glyph B 4→ℂ):Stock B:=(0,fun j=>a (curvature B j))

theorem bill (a:Glyph B 4→ℂ):
    ∑j,‖(stock B a).2 j‖ ≤ ∑i,‖a i‖:=by
  change (∑j,‖a (curvature B j)‖)≤_
  rw [←sum_image (s:=univ) (g:=curvature B) (f:=fun i=>‖a i‖) (fun _ _ _ _ h=>injective B h)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>norm_nonneg (a i))

end YM.Integration.WilsonMatrixOriginalCurvatureStock

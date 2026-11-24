import YM.Integration.WilsonOriginalPinnedDeckOrbit

/-! One common deck translation and independent relative pages for a finite
family of old connected insertions on the same physical covering board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPageOrbits
open Finset Lattice RG QuadraticLocal
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalConnectedPeriodPage WilsonOriginalLocatedDeckAction WilsonOriginalPinnedDeckOrbit
open scoped Classical BigOperators
variable {ι:Type} [DecidableEq ι] {n N:Side} (h:n.val∣N.val)
  (J:Finset ι)(a:ι)(live:a∈J)(homes:ι→Site n)(base:Fin (Pages n N))

def placed (d:Deck h)(p:(J.erase a)→Fin (Pages n N))(v:J):Fin (Pages n N):=
  if eq:v.val=a then step h (homes a) d base else
    step h (homes v.val) d (p ⟨v.val,mem_erase.mpr ⟨eq,v.property⟩⟩)

theorem root (d:Deck h)(p:(J.erase a)→Fin (Pages n N)):
    placed h J a homes base d p ⟨a,live⟩=step h (homes a) d base:=by simp [placed]

theorem relative (d:Deck h)(p:(J.erase a)→Fin (Pages n N))(v:J.erase a):
    placed h J a homes base d p ⟨v.val,mem_of_mem_erase v.property⟩=
      step h (homes v.val) d (p v):=by simp [placed,(mem_erase.mp v.property).1]

def common (u:J→Fin (Pages n N)):Deck h:=(around h (homes a) base).symm (u ⟨a,live⟩)

def unfurl:(Deck h × ((J.erase a)→Fin (Pages n N))) ≃ (J→Fin (Pages n N)) where
  toFun u:=placed h J a homes base u.1 u.2
  invFun u:=(common h J a live homes base u,fun z=>
    (steps h (homes z.val) (common h J a live homes base u)).symm
      (u ⟨z.val,mem_of_mem_erase z.property⟩))
  left_inv:=by
    rintro ⟨d,p⟩
    have head:common h J a live homes base (placed h J a homes base d p)=d:=by
      unfold common
      rw [root]
      exact (around h (homes a) base).symm_apply_apply d
    apply Prod.ext head
    funext z
    dsimp only
    rw [head,relative]
    exact (steps h (homes z.val) d).symm_apply_apply (p z)
  right_inv:=by
    intro u
    funext v
    by_cases atRoot:v.val=a
    · have eq:v=(⟨a,live⟩:J):=Subtype.ext atRoot
      subst v
      dsimp only
      rw [root]
      exact (around h (homes a) base).apply_symm_apply _
    · let z:J.erase a:=⟨v.val,mem_erase.mpr ⟨atRoot,v.property⟩⟩
      exact (relative h J a homes base _ _ z).trans
        ((steps h (homes v.val) (common h J a live homes base u)).apply_symm_apply _)

theorem physical (d:Deck h)(p:(J.erase a)→Fin (Pages n N))(v:J.erase a):
    (page h (homes v.val) (placed h J a homes base d p ⟨v.val,mem_of_mem_erase v.property⟩)).val=
      d.val+(page h (homes v.val) (p v)).val:=by rw [relative,value]

include live in
theorem average (K:(J→Fin (Pages n N))→ℂ):
    (Pages n N:ℂ)⁻¹*∑u,K u=
      (Pages n N:ℂ)⁻¹*∑d:Deck h,∑p:(J.erase a)→Fin (Pages n N),K (placed h J a homes base d p):=by
  classical
  rw [←(unfurl h J a live homes base).sum_comp K,Fintype.sum_prod_type]
  rfl

end YM.Integration.WilsonOriginalCensusPageOrbits
end

import YM.Integration.WilsonOriginalCensusPageOrbits
import YM.Integration.WilsonNeutralPointPageAverage

/-! Each lifted upper insertion uses its own fixed child digit. The common
volume in the upper relative-page sum is exactly the lower page volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusChildPages
open Finset Lattice RG Wilson
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open scoped Classical BigOperators
variable {n f N F ℓ:Side}(u:f.val=n.val*ℓ.val)(v:F.val=N.val*ℓ.val)
  (h:n.val∣N.val)(H:f.val∣F.val)(z:Site f)
local notation "r" => (Ratio.mk ℓ u : Ratio n f)
local notation "R" => (Ratio.mk ℓ v : Ratio N F)

def toFine (p:Fin (Pages n N)):Fin (Pages f F):=
  (page H z).symm ⟨(R).assemble ((page h ((r).parent z) p).val,(r).residue z),by
    rw [subdiv_marks u v h H z]
    exact mem_image.mpr ⟨_,(page h ((r).parent z) p).property,rfl⟩⟩

theorem located (p:Fin (Pages n N)):
    (page H z (toFine u v h H z p)).val=(R).assemble ((page h ((r).parent z) p).val,(r).residue z):=
  congrArg Subtype.val ((page H z).apply_symm_apply _)

theorem parent (p:Fin (Pages n N)):
    (R).parent (page H z (toFine u v h H z p)).val=(page h ((r).parent z) p).val:=by
  rw [located,Ratio.assemble_parent]

def choice:Fin (Pages n N)≃Fin (Pages f F):=Equiv.ofBijective (toFine u v h H z) (by
  constructor
  · intro p q same
    apply (page h ((r).parent z)).injective
    apply Subtype.ext
    rw [←parent u v h H z p,←parent u v h H z q,same]
  · intro q
    have actual: (page H z q).val∈parcel (splitter H) z:=(page H z q).property
    obtain ⟨y,hy,hq⟩:=mem_image.mp ((subdiv_marks u v h H z).le actual)
    let p:Fin (Pages n N):=(page h ((r).parent z)).symm ⟨y,hy⟩
    refine ⟨p,(page H z).injective (Subtype.ext ?_)⟩
    rw [located]
    have root:(page h ((r).parent z) p).val=y:=congrArg Subtype.val ((page h ((r).parent z)).apply_symm_apply _)
    rw [root]
    exact hq)

include u v in
theorem volume:Pages f F=Pages n N:=by
  unfold Pages
  rw [u,v,Nat.mul_div_mul_right _ _ ℓ.pos]

end YM.Integration.WilsonOriginalCensusChildPages
end

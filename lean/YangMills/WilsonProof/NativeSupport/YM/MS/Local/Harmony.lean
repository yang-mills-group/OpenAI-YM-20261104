import YM.MS.Local.Harmony
import YM.MS.Local.Exactness
/-!
# Extend choices of splittings at bounded h to a single linear solution

Not yet a polynomial lift in y; this is the local Taylor BV calculation.
Supports remain polynomial across charge sectors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {f : Grade G} {h q d C : ℤ}
-- All relations needed forward.
lemma partial_inv (G:Gauge) (h q:ℤ): ∃ D : Baton G, (∀ f, D f∈ yields h (q-1)) ∧ ∀ f∈ yields h (q-1), Q (D (Q f))= Q f:= by
   let M:= yields (G:=G) h (q-1); let Y:=Q.comp M.subtype
   obtain ⟨T,hT⟩:= Submodule.exists_isCompl (LinearMap.range Y)
   obtain ⟨L,hL⟩:= Y.rangeRestrict.exists_rightInverse_of_surjective Y.range_rangeRestrict
   let A:=(LinearMap.range Y).projectionOnto T hT
   refine ⟨M.subtype.comp (L.comp A),fun f=> (L (A f)).property,fun f hf=>?_⟩
   let u : LinearMap.range Y := Y.rangeRestrict (⟨f,hf⟩:M); have ha:u.val=Q f:= rfl
   change Y (L (A (Q f)))=Q f
   rw [← ha, show A u.val=u from Submodule.projectionOnto_apply_left ..]
   exact congr_arg Subtype.val (LinearMap.congr_fun hL u)

-- grade dial by product of all except x (unordered not ring of operators here)

lemma full_inv (G:Gauge) (k:ℤ): ∃ A:Baton G, ∀ h≤k, ∀ q f, f∈ yields h q → A f∈ yields h (q-1) ∧ Q (A (Q f))=Q f:= by
   let C:= Finset.Icc 0 k; let s:= Finset.Icc (-2:ℤ) 1
   choose P pH using fun h=> choose_grade G h C; choose D hD HD using partial_inv G
   let A : Baton G:= ∑ h∈C, (∑ q∈s, D h q ∘ₗ P h ∘ₗ mask q)
   have HA (h q :ℤ) (f:Grade G) (he:h ≤ k) (hf:f∈yields h q): A f=D h q f := by
       by_cases hl:f=0; · subst f; simp
       obtain ⟨hz,hq⟩:= canbe hf hl
       simp only [A,LinearMap.sum_apply,LinearMap.comp_apply]
       simp_rw [caught _ hf]; have ht : h∈C:= Finset.mem_Icc.mpr ⟨hz,he⟩; simp_rw [apply_ite,pH _ h (Or.inr ht) q _ hf,map_zero]; simp [apply_ite,ht,show q∈s from hq]
   refine ⟨A,fun h hh q f hf=> ⟨by rw [HA h q f hh hf]; exact hD .., by rw [HA h (q+1) _ hh (stays _ _ _ hf)]; exact HD h (q+1) _ (by simpa)⟩⟩
end YM.MS.Local.BV

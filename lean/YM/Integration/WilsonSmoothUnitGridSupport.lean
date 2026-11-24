import YM.Integration.WilsonSmoothUnitFiniteGrid
import Mathlib.Order.Interval.Finset.Nat

/-! Count only the projected support of the smooth unit test on the actual original
four-dimensional lattice. The signed coefficients of all surviving fields may depend
on their own positions and on the other coordinates held during this sum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSmoothUnitGridSupport
open Set Finset YM.LocalLTE.Weft WilsonSmoothUnitFiniteGrid
open scoped BigOperators Classical

theorem axis {N:ℕ}[NeZero N](left h a b:ℝ)(pos:0<h)(order:a ≤ b)
    (S:Finset (ZMod N))(whereAt:∀x∈S,point left h x∈Set.Icc a b):
    (S.card:ℝ)*h ≤ b-a+h:=by
  classical
  by_cases active:S.Nonempty
  · let U:=S.image (fun x=>(x.val:ℕ))
    have seen:U.Nonempty:=active.image _
    have inj:Function.Injective (fun x:ZMod N=>x.val):=by
      intro p q same
      change p.val=q.val at same
      rw [←ZMod.natCast_zmod_val p,←ZMod.natCast_zmod_val q,same]
    have cards:U.card=S.card:=Finset.card_image_of_injective _ inj
    have listed:∀i∈U,a ≤ left+(i:ℝ)*h ∧ left+(i:ℝ)*h ≤ b:=by
      intro i hi
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hi
      exact whereAt z hz
    have subset:U⊆Finset.Icc (U.min' seen) (U.max' seen):=by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨U.min'_le i hi,U.le_max' i hi⟩
    have raw:=Finset.card_le_card subset
    rw [cards,Nat.card_Icc] at raw
    have ends:=U.min'_le (U.max' seen) (U.max'_mem seen)
    have nc:S.card+U.min' seen ≤ U.max' seen+1:=by omega
    have sizes:(S.card:ℝ)+(U.min' seen:ℝ) ≤ (U.max' seen:ℝ)+1:=by exact_mod_cast nc
    have l:=(listed _ (U.min'_mem seen)).1
    have r:=(listed _ (U.max'_mem seen)).2
    nlinarith only [l,r,mul_le_mul_of_nonneg_right sizes pos.le]
  · have em:S=∅:=Finset.not_nonempty_iff_eq_empty.mp active
    simp [em]
    linarith

theorem four {N:ℕ}[NeZero N](h R E:ℝ)(pos:0<h)(hr:0 ≤ R)(he:0 ≤ E)
    (left lo:Fin 4 → ℝ)(M:(Fin 4 → ZMod N) → ℝ)
    (within:∀x,M x ≤ E)
    (outside:∀x,(∃j,point (left j) h (x j)∉Set.Icc (lo j) (lo j+R)) → M x ≤ 0):
    h^4*(∑x,M x) ≤ (R+h)^4*E:=by
  classical
  let S (j:Fin 4):Finset (ZMod N):=univ.filter (fun z=>point (left j) h z∈Set.Icc (lo j) (lo j+R))
  let box:=Fintype.piFinset S
  have bounded:∀i,(S i|>.card:ℝ)*h ≤ R+h:=by
    intro j
    have hh:=axis (left j) h (lo j) (lo j+R) pos (by linarith) (S j)
      (fun x hx=>(mem_filter.mp hx).2)
    linarith
  have cnt:(box.card:ℝ)*h^4 ≤ (R+h)^4:=by
    have each:=Finset.prod_le_prod (s:=univ) (f:=fun i:Fin 4=>(S i|>.card:ℝ)*h)
      (g:=fun _=>R+h) (fun i _=>mul_nonneg (Nat.cast_nonneg _) pos.le) (fun i _=>bounded i)
    simpa [box,Fintype.card_piFinset,Finset.prod_mul_distrib] using each
  have cash:(∑x,M x) ≤ (box.card:ℝ)*E:=by
    calc
      (∑x,M x) ≤ ∑x,if x∈box then E else 0:=by
        apply sum_le_sum
        intro x _
        split_ifs with hmem
        · exact within x
        · apply outside
          by_contra! allIn
          apply hmem
          exact Fintype.mem_piFinset.mpr (fun j=>mem_filter.mpr ⟨mem_univ _,allIn j⟩)
      _=_:=by simp
  calc
    _ ≤ h^4*((box.card:ℝ)*E):=mul_le_mul_of_nonneg_left cash (by positivity)
    _=((box.card:ℝ)*h^4)*E:=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_right cnt he

end YM.Integration.WilsonSmoothUnitGridSupport

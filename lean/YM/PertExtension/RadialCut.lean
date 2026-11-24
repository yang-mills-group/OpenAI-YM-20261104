import YM.PertExtension.SlotRay

/-! Turning all ordinary radial Taylor tests, simultaneously, into an exact
 unprojected off-shell label before evaluating Maxwell tensors. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.PertExtension.Heat.Ray
open Function Set Filter Finset RG Wilson Lattice Labels Source Drops Hue MvPolynomial
open Next.Rank Next.Rank.Beamer Next.Rank.Configuration Next.Rank.LiftMark Next.Rank.Normal Next.Rank.Spindle Top Push.CutoffProjectors Next.Foundations
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{d e:ℕ}{F : Labels.Frame G d} (P : poly (Panel RG.Slot G))

lemma ink_cut (k:ℕ) : print d (cut k P)=cut k (print d P) := by
   apply cut_natural; intro i; unfold print; rw [AlgHom.comp_apply,exchange_x]
   unfold ink; rw [map_sum,map_sum]
   refine IsWeightedHomogeneous.sum _ _ _ ?_; intro j hj
   simp only [glyph,Finsupp.linearCombination_single,← C_mul',map_mul,rename_C,rename_X]
   exact (isWeightedHomogeneous_X ..).C_mul _

lemma cap_comm (p : Pol G)(k : ℕ) : capRead d (cut k p)=cut k (capRead d p) := by ext i; simp only [coeff_capRead,cut_coeff];split_ifs <;> simp [*]

theorem clipped_bank {e:ℕ}(he:d≤e) {L:Label G d} (h:capRead d (print e P)=L.val) : testLM (d:=d) P = bank F (F.coords L) := by
   funext j; change testLM (d:=d) P j=probe F j (F.coords L)
   rw [probe_eq,LinearEquiv.symm_apply_apply,deriv_read,← bounded_test he, ← tier_capRead d (print e _) j.2.val (by omega),h]

private lemma basis_degree (i : F.Index) : Hue.Lone (F.basis i).val (F.grades i).2 := by
  intro _ h
  have he:= (pure_grade _ _).1 (F.pure i) h
  rw [Labels.weight_slot] at he
  simpa [Finsupp.weight_apply,smul_eq_mul] using! congr_arg Prod.snd he
private lemma cut_basis (i:F.Index)(k:ℕ): cut k (F.basis i).val = if k=(F.grades i).2 then (F.basis i).val else 0:=by
  split_ifs with ht
  · rw [ht]; apply (basis_degree i).weightedHomogeneousComponent_same
  exact (basis_degree i).weightedHomogeneousComponent_ne k ht
private def sift (k:ℕ)(L:Label G d):Label G d:= ∑ i, (if k=(F.grades i).2 then (F.coords L) i else 0) • F.basis i
-- use explicit F
private lemma sift_eq (F:Labels.Frame G d)(k:ℕ)(L:Label G d): ((sift (F:=F) k L).val)=cut k L.val:=by
  nth_rw 2 [← F.basis.sum_repr L]
  unfold sift
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower,map_sum,map_smul,cut_basis]
  exact Finset.sum_congr rfl fun i hi=> by split_ifs <;> first | rfl | simp
private lemma sift_read (F:Labels.Frame G d)(i:F.Index)(L:Label G d): (F.coords (@sift G d F (F.grades i).2 L)) i=(F.coords L) i:=by
  unfold sift; rw [map_sum,Finset.sum_apply, Finset.sum_eq_single_of_mem i (mem_univ _)]; exact (by simp [F.coords_basis])
  intro j hj h; by_cases hg:(F.grades i).2=(F.grades j).2 <;> simp [hg,F.coords_basis,h,Ne.symm h]

variable {L : Label G d}
theorem collect_normal (h: clipped d P=L.val): joint F P=F.coords L := by
    funext i; let k:=(F.grades i).2
    change reconstruct F (testLM (cut k P)) i= _
    have ht : capRead d (print d (cut k P))=(sift (F:=F) k L).val:= by rw [ink_cut,cap_comm,show capRead d _ = L.val from h];exact (sift_eq ..).symm
    rw [clipped_bank _ le_rfl (F:=F) ht,reconstruct_eq];exact sift_read ..

lemma label_verdict {he:d≤e} (h : clipped e P=(raiseLabel G he L).val) : Perch.Verdict address e P (raiseLabel G he L) := by
  unfold Perch.Verdict
  rw [costs]; apply congr_arg
  apply MvPolynomial.rename_injective (R:=ℂ) (f:=(Subtype.val:KeyIn G e→Key G)) (fun _ _ h=>Subtype.ext h)
  change _ = rename (Subtype.val : KeyIn G e → _) _; rw [returns]
  unfold key; rw [show (fun i :KeyIn G e=>generation i.val)=(generation ∘ Subtype.val) from rfl, ← trim_rename,weigh]
  exact h
end YM.PertExtension.Heat.Ray

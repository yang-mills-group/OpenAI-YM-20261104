import YM.Push.GRID_APPROXIMATION.Hit
import YM.Push.ABSOLUTE_SUMS.Basic
import YM.Next.SCHEDULE.Support
import YM.RG.ActivityBounds

/-! The regular, masked part of an actually priced activity has an oscillation
cost over the edited support, independent of the ambient volume. This is the
lightweight regular activity estimate of `Curvature.Pointwise.Read.Sensitive`,
restated for `Activities.Valid` and checked on the same native source graph. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut.FiledAction
open Function Finset Lattice Wilson RG Push Push.AbsoluteSums Next.Scheduling
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{P:BudgetPoint}{x w:ℝ}(A:Activities G n)(hp:1≤P.supportExponent)(hE:A.EBound P x)
local notation "b0"=>GridApprox.Attach.hitConstant P.B
local notation "c"=>Site n
include hp hE
private lemma sensitivity : ∃ f:ℕ→ℝ, (∀ i, P.supBounds (A.reg i).site (A.reg i).support (A.E i) (f i)) ∧ (∀ x':Site n,
    SumBudget (fun i=>if x' ∈ (A.reg i).support then f i else 0) (b0*x)) :=by
   obtain ⟨f,hf,hX⟩:= hE; let f' i := (A.reg i).support
   have hh(i):0 ≤f i:= (hf i).1
   have ht : Ac.Hit f' P.B f 0 (b0*x):=by
      refine GridApprox.Attach.root_to_hit _ _ (id:c→c) injective_id f hh (fun i:ℕ=> {(A.reg i).site}) 0 _ (budget_nonneg (hX 0)) (fun i _=>⟨_,mem_singleton.mpr rfl,(A.reg i).anchor⟩) (fun i=>?_)
      simp_rw [mem_singleton]; apply budget_mono (hX i) (fun i=>by split; exact mul_nonneg (hh _) (Real.exp_pos _).le; exact le_rfl)
      intro j; split
      next hi=> rw [show (0:ℝ)+1=1 from zero_add _, if_pos hi.symm, BudgetPoint.mass,mul_comm]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (hh j)
      next hi=> rw [if_neg (Ne.symm hi)]
   exact ⟨f,hf,fun x=> by simpa [f',Ac.Hit] using (ht x)⟩
omit hp hE
variable {A}
local notation "F" => A.regularOccurrence P
local notation "B"=> (Site n)
def Kept (U V:Config G n)(L:Support n) := ∀ i:Edge B,i.1∉ L → U i= V i
variable (P)
private lemma surrounding {U V:Config G n}{L T:Support n}(ho:Kept U V L)(h:Disjoint (halo 8 L) T) : Agrees ( inspected T ) U V:=fun i hx _=> ho _ (fun hi=>by
    obtain ⟨x,hx,h'⟩:= halo_spec.mp (flag_layer T hx); exact disjoint_left.mp h (halo_spec.mpr (by use i.1, hi; rwa [separation_comm])) hx)
private lemma united {t:Support n}{U V:Config G n}{L:Support n}(ho:Kept U V L)(h:Disjoint (halo 8 L) t) : t∩flags P.threshold U = t∩flags P.threshold V:= flags_agree _ _ _ _ ( surrounding ho h )
private lemma agreed {i:ℕ}{U V:Config G n}{L:Support n}(ho:Kept U V L)(he: P.Regular (A.reg i).support (A.E i)) (h:Disjoint (halo 8 L) (A.reg i).support) : F i U=F i V:=by
   have hv:= surrounding ho h; let s:= (A.reg i).support
   have hS: A.E i U=A.E i V:= he.sites _ _ (agrees_mono hv (fun _ hm => mem_union_left _ hm)); have hz : Healthy P.threshold s U ↔ Healthy P.threshold s V:= by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty,united P ho h]
   unfold Activities.regularOccurrence; by_cases h: Healthy P.threshold s V
   · rw [masked_eq _ _ _ _ (hz.mpr h),masked_eq _ _ _ _ h]; exact hS
   rw [masked_ne _ _ _ _ (mt hz.mp h),masked_ne _ _ _ _ h]
private theorem occurrence_bounds {i:ℕ}{b:ℝ}(bound:P.supBounds (A.reg i).site (A.reg i).support (A.E i) b)(u:Config G n):
    ‖A.regularOccurrence P i u‖≤b:=by
  by_cases ok:Healthy P.threshold (A.reg i).support u
  · rw [Activities.regularOccurrence,masked_eq _ _ _ _ ok];exact bound.2 u ok [] (Nat.zero_le _) (by simp)
  rw [Activities.regularOccurrence,masked_ne _ _ _ _ ok,norm_zero];exact bound.1

include hp in
theorem funded_edit {L: Support n} (valid:A.Valid P x w)(U V:Config G n)(ho:Kept U V L) :
    |A.additive P U-A.additive P V|≤ ((halo 8 L).card:ℝ)*(2*b0*x) :=by
   obtain ⟨f,hf,hX⟩:= sensitivity A hp valid.boundE
   let D i := (A.reg i).support
   let f₀ (i:B) j:= (if i∈ D j then f j else 0)
   let Z:= halo 8 L
   have ht:= budget_over Z f₀ (fun _=> (b0*x)) (fun i _=> hX i)
   let F₀ i:= F i U-F i V
   have Hv(i):‖F₀ i‖ ≤ 2*(∑ j∈Z,f₀ j i):= by
       unfold F₀; by_cases h: Disjoint Z (D i)
       · rw [agreed P ho (valid.regular.smooth i) h,sub_self,norm_zero]; exact mul_nonneg zero_le_two (ht.1 _)
       obtain ⟨j,hj,hv⟩:= Finset.not_disjoint_iff.mp h; have hu:=single_le_sum (f:=fun j=> f₀ j i) (fun j _=> (hX j).1 i) hj; unfold f₀ at hu; rw [if_pos hv] at hu
       refine (norm_sub_le ..).trans ((add_le_add (occurrence_bounds P (hf i) U) (occurrence_bounds P (hf i) V)).trans ?_); rw [← two_mul]; exact mul_le_mul_of_nonneg_left hu zero_le_two
   have hP : SumBudget (fun i=>‖F₀ i‖) (2*(Z.card*(b0*x))) := by
       have hw:= budget_mono (budget_scale zero_le_two ht) (fun i=> norm_nonneg _) Hv
       simpa only [sum_const,nsmul_eq_mul] using! hw
   unfold Activities.additive; rw [←Summable.tsum_sub ((Activities.ESeries valid).summable U) ((Activities.ESeries valid).summable V) ]; change ‖(∑' i,F₀ i)‖≤_
   exact (norm_tsum_le_tsum_norm hP.2.1).trans (hP.2.2.trans (le_of_eq (by unfold Z; ring)))

end YM.Integration.FVA1Physical.Exchange.RoseCut.FiledAction

import YM.Pert.Attach.Partition
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-! Exact scalar gas equation; old terms only use the threshold, no fake improvement of support exponents needed. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG Finset Filter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {A:Activities G n} {X:Corrections G n}
    {Q P:BudgetPoint} {δ w : ℝ} (hT:Q.threshold=P.threshold) (HA:A.Valid Q δ w) (hp:Prepared P.threshold X)

private lemma split_start {s U} : start A X P U s = A.gasOccurrence P s.toLeft U * ∏ j ∈ s.toRight, X.value j U := by
   unfold start Activities.gasOccurrence; split_ifs with h
   · exact prod_sum_eq_prod_toLeft_mul_prod_toRight (f:=weight A X U) s
   rw [zero_mul]

include hT HA hp
lemma total_gas {R:Activities G n} (U: Config G n) (hu:Summable (‖X.value · U‖)) :
    (attach A X P.threshold R).gas P U = A.gas Q U * ∏' j, (1+X.value j U) := by
   have hs : Summable fun t:Finset ℕ=> ‖∏ j∈t, X.value j U‖ := by
      simp_rw [norm_prod]; exact summable_finsetProd_of_summable_nonneg (fun _=>norm_nonneg _) hu
   rw [tprod_one_add hs.of_norm,Activities.gas]
   unfold Activities.gas
   have hd : A.ForcedFamily P := ⟨HA.forced.sym,HA.forced.symtest,HA.forced.meas,HA.forced.meas_test,hT ▸ HA.forced.reads,
     hT ▸ HA.forced.reads_test, hT ▸ HA.forced.permit⟩
   have he (s:Finset ℕ) : A.gasOccurrence Q s U = A.gasOccurrence P s U := by unfold Activities.gasOccurrence Activities.admissible; rw [hT]
   have H : HasSum (start A X P U)
      ((∑' s, A.gasOccurrence Q s U)*(∑' s, ∏ j∈s,X.value j U)) := by
     rw [tsum_mul_tsum_of_summable_norm ((Activities.gasSeries HA).absolute U) hs]
     let e := (@Finset.sumEquiv ℕ ℕ).toEquiv; refine e.symm.hasSum_iff.mp ?_
     have eqz (p: Finset ℕ × Finset ℕ) := split_start (A:=A) (X:=X) (P:=P) (U:=U) (s:=e.symm p)
     simp_rw [show ∀ b : Finset ℕ × Finset ℕ, (e.symm b).toLeft = b.1 from fun b => congrArg Prod.fst (e.apply_symm_apply b),
       show ∀ b : Finset ℕ × Finset ℕ, (e.symm b).toRight = b.2 from fun b => congrArg Prod.snd (e.apply_symm_apply b)] at eqz
     simp_rw [Function.comp_def,eqz,←he]
     exact ((Summable.mul_norm (Activities.gasSeries HA |>.absolute U) hs).of_norm).hasSum
   exact (gas_matched hd (hp.flag · _) R _ |>.2 H).tsum_eq
end YM.Pert.Attach

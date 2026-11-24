import YM.Integration.WilsonIndependentConditionalInsertion

/-! The native finite diagram port and Spout print on identical symmetric tensors and coupling grades. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalNotebookFilm
open WilsonCoeffUV WilsonCoeffUV.Blue RegulatorIR RegulatorIR.Diagram
open PowerSeries Finset
open scoped Classical BigOperators
variable {I:Type}[Fintype I]

theorem rank {r:ℕ}(T:RegulatorIR.Budget.Packet I r):render T=paint r T:=by
  unfold render word
  rw [paint,palm_form]
  exact Finset.sum_congr rfl fun i _=>by rw [Algebra.smul_def];rfl

theorem film {k:ℕ}{P:Orders I}(p:shellK k P):rated (fun i=>i+k) P=flash P:=by
  ext1 i
  rw [rated,flash,coeff_mk,coeff_mk,visible (n:=i+k+1) (show still (P i) (i+k+1) from fun j hj=>p i j (by omega))]
  unfold packed
  exact Finset.sum_congr rfl fun j _=>rank _

omit [Fintype I] in
theorem within {k:ℕ}{P:Orders I}(p:shellK k P)(i:ℕ):Within (i+k) (P i):=by
  intro j live
  by_contra! h
  exact live (p i j (by omega))

omit [Fintype I] in
theorem vacuum {P:Orders I}(p:shellK 2 P)(p0:P 0=0):Vacuum P:=by
  intro i j hj
  refine ⟨?_,within p i j hj⟩
  cases i with
  | zero=>exact (hj (by rw [p0];rfl)).elim
  | succ _=>omega

omit [Fintype I] in
theorem exponential {f:Ink I}(h:constantCoeff f=0):Formal.expo f=raiseE f:=by
  ext1 i
  rw [Formal.expo,coeff_mk,Formal.truncP,raises h,edit_coeff _ h _ i.lt_succ_self,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_C_mul,coeff_exp,coeff_smul]
  rw [Algebra.smul_def]
  congr 1
  norm_num [one_div,map_inv₀]

end YM.Integration.WilsonIndependentConditionalNotebookFilm

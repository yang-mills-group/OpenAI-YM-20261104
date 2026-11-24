import YM.Integration.WilsonOriginalBlissDressedField

/-! Finite simultaneous pricing of arbitrary amplitudes in the actual
reflection-positive Wilson form. Only the self-measurement of each submitted
basis field is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissGramSum
open Finset Lattice Wilson Cells
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{β:ℝ}{C:Cut n}{ι:Type*}

def combine (s:Finset ι)(c:ι→ℂ)(X:ι → Config G n → ℂ):Config G n → ℂ:=
  fun U=>∑i∈s,c i*X i U

theorem inside (s:Finset ι)(c:ι→ℂ){X:ι → Config G n → ℂ}
    (h:∀i∈s,Interior C.sector (X i)):Interior C.sector (combine s c X):=
  WilsonPositionOriginalDiagnosticReflected.addRows s fun i hi=>Interior.scale (c i) (h i hi)

theorem tested (s:Finset ι)(c:ι→ℂ){X:ι → Config G n → ℂ}
    (h:∀i∈s,Interior C.sector (X i)){Y:Config G n → ℂ}(hy:Interior C.sector Y):
    Cells.form β C (combine s c X) Y=∑i∈s,c i*Cells.form β C (X i) Y:=by
  classical
  induction s using Finset.induction_on with
  | empty=>
    rw [show combine (∅:Finset ι) c X=(fun _=>0) by funext U;simp [combine],Finset.sum_empty]
    simpa using Cells.scaleF (β:=β) (C:=C) (P:=Y) (A:=Y) 0
  | @insert i s fresh ih=>
    have hS:∀j∈s,Interior C.sector (X j):=fun j hj=>h j (mem_insert_of_mem hj)
    have inserted:combine (insert i s) c X=fun U=>c i*X i U+combine s c X U:=by
      funext U;simp [combine,fresh]
    rw [inserted,Cells.plusF (Interior.scale _ (h i (mem_insert_self _ _))) (inside s c hS) hy,
      Cells.scaleF,ih hS,Finset.sum_insert fresh]

theorem priced (s:Finset ι)(c:ι→ℂ){X:ι → Config G n → ℂ}
    (positive:Cells.Positive G β C)(h:∀i∈s,Interior C.sector (X i)):
    ‖Cells.form β C (combine s c X) (combine s c X)‖ ≤
      (∑i∈s,‖c i‖*Real.sqrt ‖Cells.form β C (X i) (X i)‖)^2:=by
  let Y:=combine s c X
  let A:=‖Cells.form β C Y Y‖
  let K:=∑i∈s,‖c i‖*Real.sqrt ‖Cells.form β C (X i) (X i)‖
  have hA:0≤A:=norm_nonneg _
  have hK:0≤K:=sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hy:Interior C.sector Y:=inside s c h
  have one (i:ι)(hi:i∈s):‖Cells.form β C (X i) Y‖≤Real.sqrt ‖Cells.form β C (X i) (X i)‖*Real.sqrt A:=by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (norm_nonneg _),Real.sq_sqrt hA]
    exact Cells.cauchy positive (h i hi) hy
  have cost:A≤K*Real.sqrt A:=calc
    A=‖∑i∈s,c i*Cells.form β C (X i) Y‖:=congrArg norm (tested s c h hy)
    _≤∑i∈s,‖c i*Cells.form β C (X i) Y‖:=norm_sum_le ..
    _≤∑i∈s,(‖c i‖*Real.sqrt ‖Cells.form β C (X i) (X i)‖)*Real.sqrt A:=by
      refine sum_le_sum fun i hi=>?_
      rw [norm_mul,mul_assoc];exact mul_le_mul_of_nonneg_left (one i hi) (norm_nonneg _)
    _=K*Real.sqrt A:=(Finset.sum_mul ..).symm
  change A≤K^2
  by_cases hr:0<Real.sqrt A
  · have hrle:Real.sqrt A≤K:=le_of_mul_le_mul_right (b:=Real.sqrt A) (by nlinarith [Real.sq_sqrt hA]) hr
    nlinarith [Real.sq_sqrt hA,sq_le_sq₀ (Real.sqrt_nonneg A) hK |>.mpr hrle]
  · have hz:Real.sqrt A=0:=le_antisymm (le_of_not_gt hr) (Real.sqrt_nonneg _)
    nlinarith [Real.sq_sqrt hA,sq_nonneg K]

end YM.Integration.WilsonOriginalBlissGramSum

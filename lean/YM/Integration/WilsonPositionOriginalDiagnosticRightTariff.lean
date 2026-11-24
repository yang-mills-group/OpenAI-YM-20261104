import YM.Integration.WilsonPositionOriginalDiagnosticRightSeries
import YM.Integration.WilsonMatrixOriginalDeckPrescriptionCash

/-! The term above the truncation of the true two-clock field program has
a before-regulator fee polynomial in its two original numerical clocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRightTariff
open Finset Matrix Polynomial MS MS.Land MS.Menus MS.Local.Physical
open WilsonMatrixOriginalDeckPrescription WilsonMatrixOriginalDeckPrescriptionSeries
open WilsonMatrixOriginalDeckPrescriptionGrowth WilsonMatrixOriginalDeckRelative
open WilsonPositionOriginalDiagnosticRightSeries WilsonMatrixOriginalDeckError
open scoped Classical BigOperators Matrix Polynomial
variable {G:Gauge}{D:Deck G}(Q:MS.Land.Prescription D)(h:ℕ)
local notation "I" => Glyph D h

private def cut {J:Type*} (p k:ℕ)(x:Accounts J):Accounts J:=if k≤p then x else fun _ _=>0

private theorem cut_pay {J:Type*} [Fintype J] [DecidableEq J] (p k:ℕ){x:Accounts J}(hx:Bound x):Bound (cut p k x):=by
  by_cases test:k≤p
  · simpa only [cut,if_pos test] using hx
  · simpa only [cut,if_neg test] using fixed (0:Matrix J J ℂ)

private def line (μ ν:ℝ)(p k:ℕ):Matrix I I ℂ:=
  (∑ a:Fin (k+1),cut p (k-a.val) (fun μ _=>fees Q h μ (k-a.val)) μ ν*
    cut p a.val (fun μ ν=>trial Q h μ ν a.val) μ ν)
    - cut p k (fun _ ν=>fees Q h ν k) μ ν

private theorem ledger (p k:ℕ):Bound (fun μ ν=>line Q h μ ν p k):=by
  apply minus _ (cut_pay p k (WilsonMatrixOriginalDeckPrescriptionCash.registered Q h k).2)
  apply total (univ:Finset (Fin (k+1)))
  intro a _
  exact multiply (cut_pay p _ (WilsonMatrixOriginalDeckPrescriptionCash.registered Q h _).1)
    (cut_pay p _ (WilsonMatrixOriginalDeckPrescriptionCash.cost Q h _))

private theorem slice (p k:ℕ)(v:ℕ→ℂ):(trunc p v).coeff k=if k≤p then v k else 0:=by
  by_cases small:k≤p
  · rw [if_pos small];exact get small v
  · simp [trunc,coeff_monomial,small,show ¬ k<p+1 by omega]

private theorem pair (p k:ℕ)(v w:ℕ→ℂ): ((trunc p v)*(trunc p w)).coeff k=
    ∑a:Fin (k+1),(if k-a.val≤p then v (k-a.val) else 0)*(if a.val≤p then w a.val else 0):=by
  rw [mul_comm,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk,←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl;intro a _
  rw [slice,slice,mul_comm]

private theorem recorded (p k:ℕ)(μ ν:ℝ)(i j:I):
    (surplus Q h μ ν p i j).coeff k = line Q h μ ν p k i j :=by
  simp only [line,surplus,Matrix.sub_apply,Matrix.mul_apply,Matrix.sum_apply,sources,change,
    Polynomial.coeff_sub,finsetSum_coeff,pair,slice]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl;intro a _
    apply Finset.sum_congr rfl;intro b _
    by_cases outer:k-a.val≤p <;> by_cases inner:a.val≤p <;> simp [cut,outer,inner]
  · by_cases small:k≤p <;> simp [cut,small]

private theorem window (p k:ℕ)(μ ν:ℝ){i j:I}
    (mem:k∈(surplus Q h μ ν p i j).support): p+1≤k ∧ k≤2*p:=by
  have hit:=Polynomial.mem_support_iff.mp mem
  constructor
  · by_contra! short
    exact hit (X_pow_dvd_iff.mp (flat Q h μ ν p i j) k short)
  · by_contra! above
    have sumzero(a:Fin (k+1)):
        cut p (k-a.val) (fun μ _=>fees Q h μ (k-a.val)) μ ν*
          cut p a.val (fun μ ν=>trial Q h μ ν a.val) μ ν=0:=by
      by_cases small:a.val≤p
      · have many:¬ k-a.val≤p:=by omega
        simp [cut,many]
      · simp [cut,small]
    have last:¬ k≤p:=by omega
    apply hit
    rw [recorded];unfold line
    rw [sum_eq_zero fun a _=>sumzero a];simp [cut,last]

private theorem cell (A:Matrix I I ℂ)(i j:I): ‖A i j‖≤amount A:=by
  apply (single_le_sum (s:=univ) (f:=fun b=>‖A i b‖) (fun _ _=>norm_nonneg _) (mem_univ j)).trans
  exact single_le_sum (s:=univ) (f:=fun a=>∑b:I,‖A a b‖) (fun _ _=>sum_nonneg fun _ _=>norm_nonneg _) (mem_univ i)

private theorem paid (p:ℕ){g:ℂ}(hg:‖g‖≤1)(μ ν:ℝ)(i j:I):
    ‖(surplus Q h μ ν p i j).eval g‖ ≤
      (∑ k∈range (2*p+1),amount (line Q h μ ν p k))*‖g‖^(p+1) :=by
  rw [eval_eq_sum]
  apply (norm_sum_le _ _).trans
  let s:=(surplus Q h μ ν p i j).support
  calc
    _ ≤ ∑ k∈s,amount (line Q h μ ν p k)*‖g‖^(p+1) := by
      apply sum_le_sum;intro k hk;rw [norm_mul,norm_pow,recorded]
      exact mul_le_mul (cell h _ i j) (pow_le_pow_of_le_one (norm_nonneg _) hg (window Q h p k μ ν hk).1)
        (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans (cell h _ i j))
    _ ≤ ∑ k∈range (2*p+1),amount (line Q h μ ν p k)*‖g‖^(p+1) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk; exact mem_range_succ_iff.mpr (window Q h p k μ ν hk).2
      · intro k _ _;exact mul_nonneg (nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ = _ :=(sum_mul ..).symm

/-- Simultaneously for all fields, clocks and all complex scalar parameters
in the unit disk, the actual chronological field product loses only its finite
original row tariff above the requested order. -/
theorem original (p:ℕ) : ∃ C:ℝ,0<C ∧ ∃d:ℕ,∀(μ ν:ℝ)(g:ℂ),‖g‖≤1→∀i j:I,
    ‖∑ b:I,(sources Q h μ p i b).eval g*(change Q h μ ν p b j).eval g -
       (sources Q h ν p i j).eval g‖ ≤ C*(size μ ν)^d*‖g‖^(p+1) :=by
  choose C hp d bound using fun k:Fin (2*p+1)=>ledger Q h p k.val
  let degree:=univ.sup d
  let fee:=1+∑ k,C k
  have cp:0<fee:=lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (sum_nonneg fun k _=>(hp k).le))
  refine ⟨fee,cp,degree,?_⟩
  intro μ ν g small i j
  have e:=paid Q h p small μ ν i j
  have costs:∑ k∈range (2*p+1),amount (line Q h μ ν p k) ≤ fee*(size μ ν)^degree :=by
    rw [←Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑ k:Fin (2*p+1),C k*(size μ ν)^degree := sum_le_sum fun k _=>(bound k μ ν).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (size_ge _ _) (le_sup (f:=d) (mem_univ k))) (hp k).le)
      _ ≤ _ :=by
        rw [←sum_mul]
        exact mul_le_mul_of_nonneg_right (by dsimp [fee];linarith) (pow_nonneg (zero_le_one.trans (size_ge _ _)) _)
  apply le_trans _ (mul_le_mul_of_nonneg_right costs (pow_nonneg (norm_nonneg _) _))
  simpa only [surplus,Matrix.sub_apply,Matrix.mul_apply,eval_sub,eval_finsetSum,eval_mul] using e

end YM.Integration.WilsonPositionOriginalDiagnosticRightTariff

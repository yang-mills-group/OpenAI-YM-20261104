import YM.Integration.FVA1Physical.Sources.Round2.DistributedFields
import YM.MSbar.Lapaz.Utopia

/-! The inherited recoil in the normalized local comparison cancels exactly for
the independently generated bank of a product of physical field stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open MeasureTheory Matrix Lattice RG RGComparison.Core16.Spool
open MSbar MSbar.Duel MSbar.Whisk MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal MSbar.Lapaz
open Push.Uniform
open Further.GaussianScalar
open scoped Classical BigOperators

theorem recoil_of_constant_seed {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (P : Matrix ι σ ℝ) {C : Matrix σ σ ℝ} (pos : C.PosDef) (Q S : SpringK ι)
    (zeroQ : Kind Q) (x : View ι) (p : ℕ) (recoil : View σ → ℝ)
    (flat : (PowerSeries.coeff 0 S).totalDegree = 0) :
    Lapaz.cov (C:=C) P Q S x recoil p = 0 := by
  let a := MvPolynomial.constantCoeff (PowerSeries.coeff 0 S)
  have constant : PowerSeries.coeff 0 S = MvPolynomial.C a :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp flat
  have incoming (w : View σ) : PowerSeries.coeff 0 (micro x P S w) = a := by
    simp only [micro,picture,PowerSeries.coeff_map,constant,MvPolynomial.eval_C]
  have hmicro (w : View σ) : Kind (micro x P (Rewind Q x) w) := by
    unfold micro Kind picture
    rw [PowerSeries.coeff_map,hush zeroQ,map_zero]
  have hv : PowerSeries.coeff 0 (Lapaz.vow P C Q x) = 1 := by
    unfold Lapaz.vow picture
    rw [PowerSeries.coeff_map,Cacao.covers (sugar _ (hush zeroQ)),map_one]
  have both := Lapaz.firm P pos Q S x (p:=p) zeroQ 0 (Nat.zero_le p)
  rw [elevator,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.sub_zero,hv,mul_one] at both
  simp_rw [elevator,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.sub_zero,
    fun w => Cacao.covers (hmicro w),mul_one,incoming] at both
  have outgoing : PowerSeries.coeff 0 (Lapaz.owes P C Q S x p) = a := by
    simpa only [integral_const,probReal_univ,one_smul] using both.symm
  unfold Lapaz.cov
  simp_rw [incoming,outgoing]
  rw [integral_mul_const,sub_self]

theorem field_recoil_zero {G : Gauge} {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (J : ι → Lamp G) (A : Mosaic.Issue G) (o : ι → Site A.f) (part : Bool)
    (P : Matrix (Joint A.F G) σ ℝ) {C : Matrix σ σ ℝ} (pos : C.PosDef)
    (Q : SpringK (Joint A.F G)) (zeroQ : Kind Q) (x : View (Joint A.F G))
    (p : ℕ) (recoil : View σ → ℝ) :
    Lapaz.cov (C:=C) P Q (jointFieldBank J A o part) x recoil p = 0 := by
  apply recoil_of_constant_seed P pos Q _ zeroQ
  rw [jointFieldBank,PowerSeries.coeff_mk]
  apply Nat.eq_zero_of_le_zero
  exact (MvPolynomial.totalDegree_rename_le ..).trans
    (lampRow_degree J part (activeSlots J A.S A.F o) 0)

end YM.Integration.FVA1Physical.Round2.Curvature

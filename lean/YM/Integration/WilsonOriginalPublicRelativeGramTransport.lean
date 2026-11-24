import YM.Integration.WilsonOriginalPublicRelativeGramPins

/-! The mixed reflected matrix recovers the actual change between the two
public fields on the complete finite quotient at a common horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramTransport
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonOriginalBlissMixedGram (grades)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    {I L:Type}[Fintype I][Fintype L](a:Axis)(h:ℕ)(J:ℝ→PhysMS.tower S)
    (basis:Module.Basis I ℂ ((Spin.comparator R.family.book).Field h))
    (r s:ℝ)(site:ℕ)(points:L→Fin 2→ Cover)(μ:L→ℂ)

private def pair (v x:S.Field h) (k:Fin 2):S.Field (grades h h k):=
  Fin.cons (α:=fun k=>S.Field (grades h h k)) v (fun _=>x) k

private def right (p:Points 2)(v:S.Field h):S.Field h→ₗ[ℂ]ℂ:=
  (S.classMoment S (grades h h) p).toLinearMap (pair R (S:=S) h v 0) (1:Fin 2)

private theorem apply_right (p:Points 2)(v x:S.Field h):
    right R (S:=S) h p v x=S.classMoment S (grades h h) p (pair R (S:=S) h v x):=by
  change S.classMoment S (grades h h) p (Function.update (pair R (S:=S) h v 0) (1:Fin 2) x)=_
  congr 1
  funext k
  fin_cases k <;> simp [pair,Function.update]

def transition:Matrix I I ℂ:=fun k j=>basis.repr ((J r h).symm (J s h (basis j))) k

private def probe (i:I):S.Field h→ₗ[ℂ]ℂ:=
  ∑m, μ m • right R (S:=S) h (Extraction.Order.grid R.family site (points m))
    (S.adj F.room.kernel.spin h a (J r h (basis i)))

omit [Fintype I] in
private theorem read (t:Bool)(i j:I):
    matrix R F a (fun _:I=>h) J (fun k=>basis k) r s site points μ t i j=
      probe R F a h J basis r site points μ i (J (cond t s r) h (basis j)):=by
  classical
  simp only [matrix,probe,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,apply_right,readings]
  rfl

theorem cross:
    matrix R F a (fun _:I=>h) J (fun k=>basis k) r s site points μ true=
      matrix R F a (fun _:I=>h) J (fun k=>basis k) r s site points μ false *
        transition R h J basis r s:=by
  classical
  ext i j
  have decompose : (∑k,transition R h J basis r s k j • J r h (basis k))=J s h (basis j):=by
    calc
      _=(J r h) (∑k,basis.repr ((J r h).symm (J s h (basis j))) k • basis k):=by simp only [transition,map_sum,map_smul]
      _=_:=by rw [basis.sum_repr,LinearEquiv.apply_symm_apply]
  rw [Matrix.mul_apply,read]
  simp only [Bool.cond_true]
  rw [← decompose,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul,read]
  simp [mul_comm]

theorem original (rank:IsUnit (matrix R F a (fun _:I=>h) J (fun k=>basis k) r s site points μ false).det):
    (matrix R F a (fun _:I=>h) J (fun k=>basis k) r s site points μ false)⁻¹ *
      matrix R F a (fun _:I=>h) J (fun k=>basis k) r s site points μ true=
        transition R h J basis r s:=by
  rw [cross,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ rank,Matrix.one_mul]

end YM.Integration.WilsonOriginalPublicRelativeGramTransport

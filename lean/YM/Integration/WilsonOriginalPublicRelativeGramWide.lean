import YM.Integration.WilsonOriginalPublicRelativeGramOptical
import YM.Integration.WilsonOriginalPublicRelativeGramReporting

/-! The wider aligned tile can carry the actual weak fields at their own
smaller radius. Its Gram inverse incurs both changes of physical frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramWide
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonOriginalBlissMixedGram (grades)
open WilsonOriginalPublicRelativeGramPins (matrix readings)
open WilsonOriginalPublicRelativeGramTransport (transition cross)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {I L:Type}[Fintype I][Fintype L](a:Axis)(h:ℕ)(J:ℝ→PhysMS.tower S)
  (basis:Module.Basis I ℂ ((Spin.comparator R.family.book).Field h))
  (r t:ℝ)(site:ℕ)(points:L→Fin 2→ Cover)(μ:L→ℂ)

private def pair (v x:S.Field h) (k:Fin 2):S.Field (grades h h k):=
  Fin.cons (α:=fun k=>S.Field (grades h h k)) v (fun _=>x) k

private def left (p:Points 2)(v:S.Field h):S.Field h→ₗ[ℂ]ℂ:=
  (S.classMoment S (grades h h) p).toLinearMap (pair R (S:=S) h 0 v) (0:Fin 2)

private theorem left_apply (p:Points 2)(v x:S.Field h):
    left R (S:=S) h p v x=S.classMoment S (grades h h) p (pair R (S:=S) h x v):=by
  change S.classMoment S (grades h h) p (Function.update (pair R (S:=S) h 0 v) (0:Fin 2) x)=_
  congr 1
  funext k
  fin_cases k <;> simp [pair,Function.update]

private def read (j:I):S.Field h→ₗ[ℂ]ℂ:=
  ∑m, μ m • left R (S:=S) h (Extraction.Order.grid R.family site (points m)) (J r h (basis j))

omit [Fintype I] in
private theorem row (i j:I):
    matrix R F a (fun _:I=>h) J (fun k=>basis k) t r site points μ true i j=
      read R h J basis r site points μ j (S.adj F.room.kernel.spin h a (J t h (basis i))):=by
  simp only [matrix,read,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,left_apply,readings]
  rfl

local notation "M" => (fun (lo hi:ℝ)=>matrix R F a (fun _:I=>h) J (fun k=>basis k) lo hi site points μ true)
local notation "T" => transition R h J basis

theorem congruence: M r r=(T t r)ᴴ * M t t * T t r:=by
  have leftward: M r r=(T t r)ᴴ * M t r:=by
    ext i j
    have decompose:(∑k,T t r k i • J t h (basis k))=J r h (basis i):=by
      calc
        _=(J t h) (∑k,basis.repr ((J t h).symm (J r h (basis i))) k • basis k):=by
          simp only [transition,map_sum,map_smul]
        _=_:=by rw [basis.sum_repr,LinearEquiv.apply_symm_apply]
    rw [Matrix.mul_apply]
    change matrix R F a (fun _:I=>h) J (fun k=>basis k) r r site points μ true i j=
      ∑k,(T t r)ᴴ i k*matrix R F a (fun _:I=>h) J (fun l=>basis l) t r site points μ true k j
    rw [row R F a h J basis r r site points μ i j,←decompose,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [row R F a h J basis r t site points μ k j,map_smulₛₗ,map_smul]
    rfl
  rw [leftward,Matrix.mul_assoc]
  congr 1
  exact cross R F a h J basis t r site points μ

variable [DecidableEq I]

theorem inverse (rank:IsUnit (M t t).det):
    IsUnit (M r r).det ∧ (M r r)⁻¹=T r t*(M t t)⁻¹*(T r t)ᴴ:=by
  have cancel₁:T r t * T t r=1:=(WilsonOriginalPublicRelativeGramOptical.compose R h J basis r t r).trans
    (WilsonOriginalPublicRelativeGramOptical.same R h J basis r)
  have cancel₂:T t r * T r t=1:=(WilsonOriginalPublicRelativeGramOptical.compose R h J basis t r t).trans
    (WilsonOriginalPublicRelativeGramOptical.same R h J basis t)
  have adjoint:(T r t)ᴴ*(T t r)ᴴ=1:=by rw [←Matrix.conjTranspose_mul,cancel₂,Matrix.conjTranspose_one]
  have sale:(T r t*(M t t)⁻¹*(T r t)ᴴ) * M r r=1:=by
    rw [congruence R F a h J basis r t site points μ]
    calc
      _ = (T r t)*((M t t)⁻¹*((T r t)ᴴ*(T t r)ᴴ))*(M t t)*(T t r):=by simp only [Matrix.mul_assoc]
      _ = _:=by rw [adjoint,Matrix.mul_one,Matrix.mul_assoc (T r t) _ (M t t),Matrix.nonsing_inv_mul _ rank,Matrix.mul_one,cancel₁]
  exact ⟨Matrix.isUnit_det_of_left_inverse sale,Matrix.inv_eq_left_inv sale⟩

theorem priced (rank:IsUnit (M t t).det){K A:ℝ}
    (paid:‖(M t t)⁻¹‖≤K)(forward:‖T r t‖≤A)(backward:‖(T r t)ᴴ‖≤A):
    IsUnit (M r r).det ∧ ‖(M r r)⁻¹‖≤(A*K)*A:=by
  obtain ⟨invert,identity⟩:=inverse R F a h J basis r t site points μ rank
  refine ⟨invert,?_⟩
  rw [identity]
  have fee:‖T r t*(M t t)⁻¹‖≤A*K:=(norm_mul_le ..).trans
    (mul_le_mul forward paid (norm_nonneg _) ((norm_nonneg _).trans forward))
  exact (norm_mul_le ..).trans (mul_le_mul fee backward (norm_nonneg _) ((norm_nonneg _).trans fee))

end YM.Integration.WilsonOriginalPublicRelativeGramWide

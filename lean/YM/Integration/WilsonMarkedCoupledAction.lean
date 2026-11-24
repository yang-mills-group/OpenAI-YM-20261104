import YM.Integration.WilsonMarkedCoupledPolynomial
import YM.Integration.WilsonMarkedHeldPolarization
import YM.PertExtension.Uniform

/-! Comparison of the genuine mixed action tensor with an independently
filed angular polynomial, keeping every field-independent vacuum coefficient
until the original centered operation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedCoupledAction
open Function Finset Tensor MvPolynomial FormalBulk08 FormalBulk08.Lava
open PertExtension.Series AllOrder.Fire WilsonMarkedCoupledPolynomial
open scoped Classical ContDiff
variable {X V:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype V]

def resting (X:Type) [NormedAddCommGroup X] [NormedSpace ℝ X] :(ℝ×X)→L[ℝ](ℝ×X):=
  (ContinuousLinearMap.fst ℝ ℝ X).prod 0

def center {d:ℕ} (A:T (ℝ×X) ℝ d): T (ℝ×X) ℝ d:=
  A-A.compContinuousLinearMap (fun _=>resting X)

theorem centered {d:ℕ} (A:T (ℝ×X) ℝ d) (x:ℝ×X):
    diagonal (center A) x=diagonal A x-diagonal A (x.1,0):=rfl

theorem center_sym {d:ℕ} {A:T (ℝ×X) ℝ d} (s:Sym A):Sym (center A):=by
  intro v t
  change A (v ∘ t)-A ((fun i=>resting X (v i)) ∘ t)=A v-A (fun i=>resting X (v i))
  rw [s v t,s _ t]

def debt (F:ℝ×X→ℝ)(L:X→L[ℝ](V→ℝ))(d:ℕ)(P:MvPolynomial V ℝ):T (ℝ×X) ℝ d:=
  center (-Tensor.symmetrize (Tensor.coeff F d 0)-stamp L d P)

theorem signed (F:ℝ×X→ℝ)(L:X→L[ℝ](V→ℝ))(d:ℕ)(P:MvPolynomial V ℝ):Sym (debt F L d P):=by
  apply center_sym;intro v t
  simp only [sub_apply,neg_apply]
  rw [symmetrize_sym _ v t,symmetric L d P v t]

theorem slice (F:ℝ×X→ℝ)(L:X→L[ℝ](V→ℝ))(d:ℕ)(P:MvPolynomial V ℝ)
    (tail:∀r,d<r→marble r P=0)(z:X):
    diagonal (debt F L d P) ((1:ℝ),z) =
      (-Radial.jet F d ((1:ℝ),z)+Radial.jet F d ((1:ℝ),0))-
      (MvPolynomial.eval (L z) P-MvPolynomial.eval 0 P):=by
  rw [debt,centered]
  have value (y:X):diagonal (-Tensor.symmetrize (Tensor.coeff F d 0)-stamp L d P) ((1:ℝ),y)=
      -Radial.jet F d ((1:ℝ),y)-MvPolynomial.eval (L y) P:=by
    change -diagonal (Tensor.symmetrize _) ((1:ℝ),y)-diagonal (stamp L d P) ((1:ℝ),y)=_
    rw [symmetrize_diagonal,filed L d P tail]
    rfl
  rw [value,value,map_zero];ring

theorem observed (F:ℝ×X→ℝ)(L:X→L[ℝ](V→ℝ))(d:ℕ)(P:MvPolynomial V ℝ)
    (tail:∀r,d<r→marble r P=0){C:ℝ}
    (cost:Prices d C (fun z:X=>(-Radial.jet F d ((1:ℝ),z)+Radial.jet F d ((1:ℝ),0))-
      (MvPolynomial.eval (L z) P-MvPolynomial.eval 0 P))):
    ‖debt F L d P‖≤Planned.AtomRegular.polarCost d*(C*2^d):=
  WilsonMarkedHeldPolarization.complete _ cost (slice F L d P tail) (signed F L d P)

end YM.Integration.WilsonMarkedCoupledAction
end

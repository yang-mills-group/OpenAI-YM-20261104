import YM.RG11Proof.Nodes.Forest
import YM.RG11Proof.Jets.Change
/-!
# Enquiries after testing the shape

Point & derivative & held exterior evaluations converted by taking
an algebraic linear map on separation distributions over coefficients.
Such a map commutes with composition and finite FPS products with
numerical field matrices; no analytic continuity with respect to test
topology is inferred for that algebraic extension. No quantitative
application to actual approximate distributions implied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Nodes
open PowerSeries YM.RG11.Jets
open scoped Classical BigOperators
variable {J T R : Type*}{n:ℕ}[CommRing R][AddCommGroup T][Module R T]

/-- For a tested distribution array. Includes any atomic tests in T and
later point & derivative evaluation coordinates may be represented by ψ.
The functional depends ONLY on perturbation-free geometry/formal probes,
not the actual coupling; within common evaluated space. -/
def perceive (A:ℕ→ reading J (T→ₗ[R] R) n)(ψ:(T→ₗ[R] R)→ₗ[R] R): reading J (PowerSeries R) n:=
   fun v=> PowerSeries.mk fun k=>ψ (A k v)

variable [Fintype J]
/-- If coefficient functional identity holds when evaluating through N
on T, it holds on every `perceive` in this fixed vector space at the
same truncation (only formal claim). Include all slots including stress
candidate basis slots if trying to convert a Ward normalization. -/
 theorem extend_questions {N}{p:Change R J}(h:Anchored p.g){A B:ℕ→ reading J (T→ₗ[R] R) n}
    (H:∀ t:T,∀v:Fin n→J, Through N (plant p.Z (fun w=> PowerSeries.subst p.g (mk (fun k=> A k w t))) v) (mk (fun k=> B k v t)) )
    (ψ:(T→ₗ[R] R)→ₗ[R] R)(v:Fin n→J): Through N (plant p.Z (fun w=>PowerSeries.subst p.g (perceive A ψ w)) v) (perceive B ψ v):=by
    intro k hk
    let X:=Finset.HasAntidiagonal.antidiagonal k
    let Y (i:ℕ):= Finset.range (i+1)
    let V:T→ₗ[R] R:=
      ∑ w:Fin n→J,∑ z∈X,coeff z.2 (cross p.Z v w) • (∑ c∈Y z.1, coeff z.1 (p.g^c) • A c w)
    have he (φ:(T→ₗ[R] R)→ₗ[R] R): coeff k (plant p.Z (fun w=>PowerSeries.subst p.g (perceive A φ w)) v)=φ V:=by
      unfold V plant; rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro w _
      rw [map_sum,coeff_mul]; apply Finset.sum_congr rfl; intro z _
      rw [map_smul,map_sum,coeff_compose z.1 _ _ h,smul_eq_mul,mul_comm _ ((coeff z.2) _)]; congr 1
      apply Finset.sum_congr rfl; intro c _; rw [map_smul,smul_eq_mul,perceive,coeff_mk,mul_comm]
    have hV : V=B k v:=by
       ext1 t
       have ht:= H t v k hk
       exact (he (LinearMap.applyₗ t)).symm.trans (ht.trans (coeff_mk ..))
    rw [he,hV,perceive,coeff_mk]
end YM.RG11.Nodes

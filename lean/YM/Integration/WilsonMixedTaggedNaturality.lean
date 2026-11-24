import YM.RG05Readout.Many.Consider
import YM.Next.MULTISOURCE.Monomial

/-! Each dated physical aggregation commutes with either specialization of a
root alternative. Scalars from engineering dilation stay attached to each
physical fine name. This is an identity on the complete polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedNaturality
open Finset Function Marker RG05Readout.Many
open scoped BigOperators Classical

variable {U V W : Type} [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable {A : Census U} {B : Census V} {C : Census W}

private theorem atoms (x : A.Mode) (a : ℂ) :
    Poly.send x a = a • (∏ i ∈ x.val, Poly.send (A.fire i) (1:ℂ)) := by
  ext y
  rw [Poly.part_send,Poly.part_smul,YM.Multi.monomial]
  simp only [Finset.prod_const_one,Subtype.ext_iff]
  split <;> simp_all

theorem agree (L M : Poly A →ₐ[ℂ] Poly B)
    (h : ∀ u, L (Poly.send (A.fire u) 1) = M (Poly.send (A.fire u) 1)) (p : Poly A) :
    L p = M p := by
  rw [← Poly.studs p,map_sum,map_sum]
  apply sum_congr rfl
  intro x _
  rw [atoms,map_smul,map_smul,map_prod,map_prod]
  exact congrArg (fun q=>p.part x • q) (prod_congr rfl fun u _=>h u)

variable {D : Type} [DecidableEq D] {R : Census D}

theorem square {a : U → V} {b : V → W} {c : U → D} {d : D → W}
    (ha : License B A a) (hb : License C B b) (hc : License R A c) (hd : License C R d)
    (x : U → ℂ) (y : V → ℂ) (z : U → ℂ) (v : D → ℂ)
    (root : ∀ i,b (a i)=d (c i)) (scalar : ∀ i, y (a i)*x i=v (c i)*z i) (p : Poly A) :
    feed y hb (feed x ha p) = feed v hd (feed z hc p) := by
  apply agree ((feed y hb).comp (feed x ha)) ((feed v hd).comp (feed z hc))
  intro i
  simp only [AlgHom.comp_apply,feed_fire,mul_one,root,scalar]

end YM.Integration.WilsonMixedTaggedNaturality

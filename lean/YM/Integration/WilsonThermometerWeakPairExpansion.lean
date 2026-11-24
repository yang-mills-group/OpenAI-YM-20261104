import YM.Integration.WilsonThermometerWeakPairForms

/-! Simultaneous finite expansion of the original clustered observable
and its child sum, with the same independent far charge in each term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairExpansion
open Function Finset Table Spec OPE OPE.Prescription OPE.Orbits
open WilsonThermometerWeakPairForms
open scoped Classical BigOperators
variable {G:Gauge}{L:Register G}{S:Table L}(T:Table L){Q:DiffPlan S}
    (P:Prescription Q){I:Type}[Fintype I]{d:I→ℕ}
def residual (h:ℕ)(x:I→E4)(o:E4)(v:Labels S d)(z:E4){e:ℕ}(w:S.Field e):ℂ:=
  discrepancy T h x o v (shadowOld P h x o v) (sole z) (sole w:Labels S (fun _:Unit=>e))

theorem original (hp:P.Coherent)(ht:T.Hierarchy)(hs:S.Hierarchy)(h:ℕ)(x:I→E4)(o:E4)
    (v:Labels S d)(z:E4){e:ℕ}(w:S.Field e)
    (live:Injective (beside x (sole z)))(outer:Injective (beside (sole o) (sole z))):
    residual T P h x o v z w=∑a:Lot Q d,∑b:↥(bands Q e),
      (weight P a v*P.test b.1 e w)*residual T P h x o (field P a) z (P.loaded b.1 e):=by
  let Far:=fixedFar (d:=d) T P h x o (sole z) (sole w:Labels S (fun _:Unit=>e))
  have eq(v:Labels S d): Far v=residual T P h x o v z w:=far_eq T P hs ..
  rw [←eq,unfolded P hp Far v]
  apply Finset.sum_congr rfl
  intro a _
  rw [eq];let M:=fixedNear T P h x o (field P a) z e
  have near (v':S.Field e):M v'=residual T P h x o (field P a) z v':=near_eq T P ht _ _ _ _ _ _ live outer
  have allw:w=∑b:↥(bands Q e),P.test b.1 e w • P.loaded b.1 e:=
    ((Finset.sum_attach (bands Q e) (fun b=>P.test b e w • P.loaded b e)).trans ((hp e).rebuilds w)).symm
  rw [←near]
  conv_lhs => rw [show M w=M (∑b:↥(bands Q e),P.test b.1 e w • P.loaded b.1 e) from congrArg M allw]
  rw [map_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _=>by rw [map_smul,smul_eq_mul,near,mul_assoc]
end YM.Integration.WilsonThermometerWeakPairExpansion
end

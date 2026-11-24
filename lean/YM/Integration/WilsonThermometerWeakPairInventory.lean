import YM.Integration.WilsonThermometerWeakPairExpansion

/-! Restoring source amplitudes on both sides of the signed subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairInventory
open Function Finset Table Spec OPE OPE.Prescription OPE.Orbits
open WilsonThermometerWeakPairForms WilsonThermometerWeakPairExpansion
open scoped Classical BigOperators
variable {G:Gauge}{L:Register G}{S:Table L}(T:Table L){Q:DiffPlan S}
    (P:Prescription Q){I:Type}[Fintype I]{d:I→ℕ}
def rent (j:ℕ)(s:ℝ)(v:S.Field j):ℝ:=∑a:↥(bands Q j),‖P.test a.1 j v‖/s^a.1.fst

theorem original (hp:P.Coherent)(ht:T.Hierarchy)(hs:S.Hierarchy)(h:ℕ)(x:I→E4)(o:E4)
    (v:Labels S d)(z:E4){e:ℕ}(w:S.Field e)
    (live:Injective (beside x (sole z)))(outer:Injective (beside (sole o) (sole z)))
    {r t D:ℝ}(rp:0<r)(tp:0<t)
    (bought:∀(a:Lot Q d)(b:↥(bands Q e)),(∏i,r^(a i).1.fst)*t^b.1.fst*
      ‖residual T P h x o (field P a) z (P.loaded b.1 e)‖≤D):
    ‖residual T P h x o v z w‖ ≤ (∏i,rent P (d i) r (v i))*rent P e t w*D:=by
  let A(a:Lot Q d):ℝ:=∏i,‖P.test (a i).1 (d i) (v i)‖/r^(a i).1.fst
  let B(b:↥(bands Q e)):ℝ:=‖P.test b.1 e w‖/t^b.1.fst
  have allA:∑a:Lot Q d,A a=∏i,rent P (d i) r (v i):=by
    simpa only [Fintype.piFinset_univ,A,rent] using (Finset.prod_univ_sum (fun i:I=>(univ:Finset (↥(bands Q (d i)))))
      (fun i b=>‖P.test b.1 (d i) (v i)‖/r^b.1.fst)).symm
  have one (a:Lot Q d)(b:↥(bands Q e)):
      ‖(weight P a v*P.test b.1 e w)*residual T P h x o (field P a) z (P.loaded b.1 e)‖≤A a*B b*D:=by
    let m:ℝ:=(∏i,r^(a i).1.fst)*t^b.1.fst
    have pos : 0 < m :=mul_pos (Finset.prod_pos fun i _=>pow_pos rp _) (pow_pos tp _)
    have price:‖residual T P h x o (field P a) z (P.loaded b.1 e)‖≤D/m:=
      (le_div_iff₀ pos).mpr ((mul_comm ..).trans_le (bought a b))
    rw [norm_mul,norm_mul]
    apply (mul_le_mul_of_nonneg_left price (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
    apply le_of_eq
    dsimp [A,B,m,WilsonThermometerWeakPairForms.weight]
    rw [Complex.norm_prod,Finset.prod_div_distrib]
    ring
  rw [WilsonThermometerWeakPairExpansion.original T P hp ht hs h x o v z w live outer]
  refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum fun a _=>(norm_sum_le ..).trans
    (Finset.sum_le_sum fun b _=>one a b)) ?_)
  rw [←allA];change _ ≤ (∑a,A a)*(∑b,B b)*D
  simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact le_of_eq (Finset.sum_comm ..)
end YM.Integration.WilsonThermometerWeakPairInventory
end

import YM.MSbar.Rolling.Tapes
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.MvPolynomial.Homogeneous
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Set Rolling Price Bakery Cacao Portal
open scoped Topology Classical BigOperators ContDiff
variable {X F:Type}
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "G"=>PowerSeries ℝ
local notation "µ"=> PowerSeries.coeff
open PowerSeries
variable (C: PowerSeries ℝ)(n:ℕ)
local notation "p!"=>taste n
lemma profit (X:ℝ→F→Prop) : Price X 0 (fun x y=> taste n C x):=by
    apply (Price.fromConst (Belt n C)).bounds; filter_upwards [width] with x ⟨hv,he,hF⟩ y hy; exact (taste_pays hv.le he C).trans (le_abs_self _)
lemma single (y:ℝ)(n:ℕ): taste n (1:PowerSeries ℝ) y=1:=by unfold taste; rw [Finset.sum_range_succ']; simp [PowerSeries.coeff_one]
variable {C n}
def Approx (F:ℝ→ℝ)(Y:PowerSeries ℝ)(n:ℕ):Prop:= Price (fun _ (_:Unit)=>True) (n+1) (fun x _=>F x-taste n Y x)
variable {G' F':ℝ→ℝ}{K:PowerSeries ℝ} (h:Approx F' C n)(hk:Approx G' K n)
namespace Approx
include h
lemma gives : Price (fun x (_:Unit)=>True) 0 (fun x _=>F' x):=((h.poorly (Nat.zero_le _)).nsum (profit C n _)).egress (Eventually.of_forall (fun x _ _=> sub_add_cancel _ _)) -- field notation reduc
lemma budget {t:ℕ}(hx:t≤n):Approx F' C t := by
   have hk : Price (fun _ (_:Unit)=>True) (t+1) (fun x _=> taste n C x-taste t C x):=by
       let e:=n-t; have he:n+1=t+1+e:=by unfold e;omega
       let f(i:ℕ)(x:ℝ)(_:Unit):=x^(t+1+i)*µ (t+1+i) C; refine (Price.bag (Finset.range e) f (fun i _=>?_)).egress (Eventually.of_forall (fun x _ _=>?_))
       · exact (((Price.xrise _ (t+1+i)).product (fromConst _)).poorly (by omega))
       unfold taste; rw [he,Finset.sum_range_add,add_sub_cancel_left]
   exact ((Price.poorly h (Nat.add_le_add_right hx _)).nsum hk).egress (Eventually.of_forall fun x _ _=> by ring)
include hk
lemma mul : Approx (fun x =>F' x*G' x) (C*K) n := by
    have hx:= Price.product h (gives hk); have ht:= Price.product hk (profit C n _)
    have hv: Price (fun x (_:Unit)=>True) (n+1) (fun x _=> taste n (C*K) x -taste n C x*taste n K x):= Price.fixed 0 (Belt n C* Belt n K) (width.mono (fun x he _ _ => (taste_mul n x he.1.le he.2.1 ..).trans_eq (by ring)))
    exact ((hx.nsum ht).cut hv).egress (Eventually.of_forall fun x _ _=>by ring)
omit hk
lemma powA (m:ℕ) : Approx (fun x=> F' x^m) (C^m) n:=by induction m with
    | zero=> unfold Approx; simp_rw [pow_zero, single,sub_self];exact nil
    | succ i ih=> unfold Approx; simp_rw [pow_succ]; exact Approx.mul ih h
variable (h₀:µ 0 C=1)
lemma tends (A:ℝ)(ha:0<A) : ∀ᶠ x in Γ,|F' x-µ 0 C|<A := by
   have hz :Price (fun _ (_:Unit)=>True) 1 (fun x _=>taste n C x -µ 0 C):= ((xunit _).product (fromConst (Belt n C))).bounds (width.mono (fun x he _ _=> (sauce C n he.1.le he.2.1).trans (le_abs_self _)))
   have hg : Price (fun _ (_:Unit)=>True) 1 (fun x _=> F' x-µ 0 C):=((Price.poorly h (by omega : 1 ≤ n+1)).nsum hz).egress (Eventually.of_forall (fun x _ _=>by ring))
   exact (hg.reach A ha (by omega)).mono fun x he=> he () trivial
include h₀
lemma little : ∀ᶠ x in Γ, (1:ℝ)/2 ≤ F' x∧ F' x ≤ 2:=by
   filter_upwards [tends h (1/2) (by norm_num)] with x he; rw [h₀] at he; obtain ⟨ha,hb⟩:= abs_le.mp he.le; constructor<;> linarith
lemma invA : Approx (fun x=> (F' x)⁻¹) C⁻¹ n:=by
   let g(x):= taste n C⁻¹ x; have hp : Approx g C⁻¹ n:=by unfold Approx g; simp_rw [sub_self];exact nil
   have he : C*C⁻¹=1:=PowerSeries.mul_inv_cancel _ (by rw [← coeff_zero_eq_constantCoeff_apply,h₀]; norm_num)
   obtain ⟨v,hv⟩:= Approx.mul h hp; refine Price.fixed v 2 ?_; filter_upwards [hv, little h h₀,width] with x hX ⟨hx,he'⟩ H y hy; have hT:= hX () trivial; rw [he,single] at hT; change ‖(F' x)⁻¹-g x‖ ≤ _; have hu: 0 < F' x:=lt_of_lt_of_le (by norm_num) hx
   rw [show (F' x)⁻¹-g x=(1-F' x*g x)/F' x from (by field_simp),norm_div,Real.norm_of_nonneg hu.le, div_le_iff₀ hu,norm_sub_rev]; apply hT.trans; have hk:=H.1; have hb:=zero_le_one.trans H.2.2; nlinarith only [hx, mul_nonneg (pow_nonneg hk.le (n+1)) (pow_nonneg hb v)]
end Approx
lemma manifest (n:ℕ)(C: PowerSeries ℝ) : Approx (taste n C) C n:=by unfold Approx; simp_rw [sub_self];exact nil
end YM.MSbar.Wave

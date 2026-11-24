import YM.Contacts.Model.Land
/-! Local sawtooth test avoiding differentiation of the LISTING in another volume.
 No Euclidean shell seam asserted. Entirely discrete. -/
noncomputable section
namespace YM.Contacts.Model.Slope
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{m:Side}{n k:ℕ}{p:PlaqAxes}
local notation "d" => (m.val)
variable (hm:m.val=2*n)
def saw (n:ℕ)(x: Per m):ℝ:= Slide.point n x
include hm
lemma following (x:Per m): ‖saw n (x+1) - saw n x‖≤1 := by
   let f:= Slide.cognac hm.ge; have hp:= f.step x; have he y:saw n y=(f.pos y:ℝ):= by simp [f, Slide.cognac,saw]
   rw [he,he]; rcases hp with h|h|h <;> simp [h] -- sub
lemma pathBound (x:Per m) (k:ℕ): ‖saw n (x+(k:Per m)) - saw n x‖ ≤ k := by
   induction k with | zero=> simp | succ k h=> push_cast; rw [← add_assoc]; exact (norm_sub_le_norm_sub_add_norm_sub _ (saw n (x+(k:Per m))) _).trans ((add_le_add (following hm _) h).trans_eq (add_comm ..))
lemma pathBound' (x:Per m)(i:ℤ): ‖saw n (x+(i:Per m)) - saw n x‖ ≤ (i.natAbs:ℝ) := by
   by_cases hi:0≤ i
   · lift i to ℕ using hi; simpa using pathBound hm x i
   let k:=i.natAbs; have hk: i= -(k:ℤ):=by omega
   have hr:=pathBound hm (x+(i:Per m)) k; rw [show x+(i:Per m)+(k:Per m)=x from (by rw [hk]; push_cast; abel)] at hr; rw [norm_sub_rev] at hr; exact hr
omit hm
-- cheap cardinal via choose strip finite ranges
def openBank (n R:ℕ)(i:Per m): Prop := (R ≤ i.val ∧ i.val+R ≤ n) ∨ (n+R≤ i.val ∧ i.val+R < 2*n)
def hand (n:ℕ)(i:Per m): ℝ := if i.val≤ n then 1 else -1
private lemma val_c (x:Per m) (i:ℤ) (a:0≤ (x.val:ℤ)+i) (b:(x.val:ℤ)+i< m.val): ((x+(i:Per m)).val:ℤ)=(x.val:ℤ)+i:= by
   let k:= ((x.val:ℤ)+i).toNat; have hk: (k:ℤ)= x.val+i:=Int.toNat_of_nonneg a; have ht:k< m.val:=by omega
   have hh : x+(i:Per m)=(k:Per m):= by
      calc x+(i:Per m) = (( (x.val:ℤ)+i :ℤ):Per m):= by push_cast; simp only [ZMod.natCast_zmod_val]
           _ = _ := by rw [← hk]; norm_cast
   rw [hh,ZMod.val_natCast_of_lt ht]; exact hk
include hm
lemma bears {x:Per m}{i:ℤ}(hh:i.natAbs≤k) (he: openBank n k x): saw n (x+(i:Per m))-saw n x=hand n x * (i:ℝ) := by
    unfold openBank at he; have ha:=val_c x i; have hp:(↑(x+(i:Per m)).val:ℤ)=(x.val:ℤ)+i:=ha (by omega) (by have hx:= ZMod.val_lt x; omega)
    have hz:(x+(i:Per m)).val< m.val:=ZMod.val_lt _; have hx:= ZMod.val_lt x; unfold saw Slide.point hand; split_ifs <;> simp only [one_mul,neg_mul] <;> norm_cast <;> simp only [Int.subNatNat_eq_coe] <;> omega
private def closure (m:Side) (n:ℕ) (R:ℕ): Finset (Per m):= (univ:Finset _).filter fun x=> ¬openBank n R x
def charge (R:ℕ):ℕ:=3*(2*R+1)
-- use lift to range centered by n times 0,n,2*n. nat values retrieve.
lemma counted (R:ℕ): (closure m n R).card ≤ charge R := by
    let d' (i:ℕ):= Finset.Icc (i-R) (i+R); let u:= d' 0 ∪ d' n ∪ d' (2*n)
    have he (i): (d' i).card≤ 2*R+1:= by unfold d'; rw [Nat.card_Icc]; omega
    have hf : (closure m n R).card ≤ u.card:= by
      apply Finset.card_le_card_of_injOn ZMod.val (fun i hi=> ?_) (ZMod.val_injective _).injOn
      unfold u d'; have h:= (mem_filter.mp (show i∈_ from hi)).2
      simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_Icc]; unfold openBank at h; push Not at h; have hz:=ZMod.val_lt i; omega
    apply hf.trans; apply (Finset.card_union_le _ _).trans; unfold charge; have hx:= Finset.card_union_le (d' 0) (d' n); have hT:= he 0; have hv:= he n; have hh:=he (2*n); omega
omit hm
lemma sign_price (x: Per m) : hand n x*hand n x=1 ∧ ‖hand n x‖=1:= by unfold hand; split <;> simp
-- volume quantity
abbrev Tail (m : Side) := Fin 3 → Per m
def ev (m:Side): Site m ≃ Per m × Tail m:= ⟨fun x=>(x 0,Fin.tail x), fun x=> Fin.cons x.1 x.2,fun x=> Fin.cons_self_tail x,fun ⟨a,b⟩=>Prod.ext (by simp) (by ext; simp)⟩
lemma sumP (f:Site m→ℝ) : (∑ x: Site m,f x)=∑ i:Per m,∑ j: Tail m,f ((ev m).symm (i,j)):= by rw [← Equiv.sum_comp (ev m).symm f,Fintype.sum_prod_type]
abbrev rate (m:Side):ℝ:=(m.val:ℝ)^3
lemma tailK (m:Side) : (Fintype.card (Tail m):ℝ) = rate m := by simp [Tail,Per,rate]
lemma head_fin (i:Per m)(j:Tail m): ((ev m).symm (i,j) 0) =i:= rfl

include hm
lemma sizeBay (f:Site m→ℝ){k:ℕ}{C:ℝ}(he: ∀ x:Site m, openBank n k (x 0) → f x=0)(hc:0≤C)(hf: ∀ x, ‖f x‖ ≤ C): ‖∑ i:Site m,f i‖ ≤ (charge k:ℝ)*rate m * C:= by
   rw [sumP]; let V:=closure m n k; let g i:= ∑ j:Tail m,f ((ev m).symm (i,j)); have ht i: ‖g i‖≤rate m*C:=by
      refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> C) (fun i _=> hf _)).trans ?_); rw [sum_const,nsmul_eq_mul,card_univ,tailK]
   have hp i (hi : i∉V): g i=0:= by
      apply Finset.sum_eq_zero; intro j _; apply he; rw [head_fin]; apply Classical.byContradiction; intro h; exact hi (mem_filter.mpr ⟨mem_univ _,h⟩)
   change ‖∑ i,g i‖≤_; rw [← sum_subset (subset_univ V) (fun i _ hi=>hp i hi)]; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>rate m*C) (fun i _=> ht i)).trans ?_); rw [sum_const,nsmul_eq_mul, mul_assoc]; apply mul_le_mul_of_nonneg_right _ (by unfold rate; positivity); exact_mod_cast counted hm _
lemma limited (v:ℤ): (let f (x:Site m):= (saw n (x 0+(v:Per m))-saw n (x 0))^2-(v.natAbs:ℝ)^2; ‖∑ i:Site m,f i‖) ≤ rate m * (charge v.natAbs:ℝ)*(v.natAbs:ℝ)^2 := by
   rw [mul_comm (rate m)]; let V:(Site m)→ℝ:=fun x=> saw n (x 0); dsimp only; apply sizeBay hm _ _ (sq_nonneg _); swap; · intro i he; rw [bears hm (le_refl v.natAbs) he,mul_pow,pow_two (hand ..),(sign_price _).1,one_mul]; exact sub_eq_zero.mpr (by have hh:|(v:ℝ)|=(v.natAbs:ℝ):= (by rw [Nat.cast_natAbs,Int.cast_abs]); rw [← hh,sq_abs])
   intro i; rw [Real.norm_eq_abs]; apply abs_le.mpr; exact ⟨by linarith only [sq_nonneg (saw n (i 0+(v:Per m))-saw n (i 0))], by have h:= pow_le_pow_left₀ (norm_nonneg _) (pathBound' hm (i 0) v) 2; rw [Real.norm_eq_abs,sq_abs] at h; linarith only [h, sq_nonneg ((v.natAbs):ℝ)]⟩
end YM.Contacts.Model.Slope

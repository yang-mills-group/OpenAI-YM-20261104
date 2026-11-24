import YM.RGComparison.Core16.Forge.Covers
/-!
# Deterministic ring replacement
Vol comparison at nonempty position requires only selected set is localized, not displacement of
full field. Keep quantitative entropy for probability estimator. Filling inner ball regardless of
original fine singularities, preserve true exterior tags by coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Push.AbsoluteSums.Animals
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {S : Side} {ι k T : Type} [Fintype ι] [Fintype k] [Fintype T]
variable {X:Prices} {B:Base G S ι k T}{g D : ℝ} (H:B.Admits X g)

def threat (loc:ι→Site S)(z:Site S)(x:Sky G ι)(R:ℕ):= ∑ i∈neighborsOf loc R z, nib x i
def weights (X:Prices)(R:ℕ): ℝ := ((ballCost R* X.K:ℕ):ℝ)
abbrev dam (X:Prices):= X.D*weights X X.b
lemma weights_pos (X:Prices) (R:ℕ):0<weights X R:=Nat.cast_pos.mpr (mul_pos (neighbors_ge R) X.K_pos)
lemma dam_pos : 0 < dam X:= mul_pos X.D_pos (weights_pos _ _)
lemma weights_mono (X:Prices): Monotone (weights X):= fun i j h=>by unfold weights ballCost; gcongr
lemma threat_nonneg (loc:ι→Site S)(z:Site S)(x:Sky G ι)(R:ℕ):0≤ threat loc z x R:= sum_nonneg fun _ _=> Base.nib_nonneg ..

namespace Base
include H
lemma tax (x:Sky G ι)(z:Site S) (R:ℕ) {t:T}(ht:0< B.choices t x):
    threat B.loc z x R ≤ X.D*g^2*weights X R+ dam X * ∑ j∈neighborsOf B.band (R+X.b) z, B.cost t x j:=by
    refine (sum_le_sum (fun i _=> H.min x t i ht)).trans ?_
    rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_add]; apply add_le_add
    · rw [mul_right_comm,←mul_assoc]; gcongr; exact X.D_pos.le; exact price_cover' H R z
    · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (window_cost _ H.core _ (H.generates x t) ..) X.D_pos.le
where
   price_cover' {X:Prices}{B:Base G S ι k T}{g:ℝ} (h:B.Admits X g)(R:ℕ)(z:Site S): ((neighborsOf B.loc R z).card:ℝ) ≤ weights X R:= Nat.cast_le.mpr <| price_cover h.core _ _

lemma fill_price {x y:Sky G ι} {z:Site S} {R:ℕ} {t:T}(ht:0<B.choices t y)(hy:∀ i∈neighborsOf B.loc R z,nib y i≤g^2)(he:∀ i∉neighborsOf B.loc R z, x i=y i):
     ∑ j∈neighborsOf B.band (R+X.b) z, B.cost t y j ≤
       X.D*g^2*weights X (R+X.b) + dam X * (g^2*weights X R + threat B.loc z x (R+X.b+X.b)-threat B.loc z x R):=by
   refine (sum_le_sum (fun j _=> H.max y t j ht)).trans ?_
   rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_add]; apply add_le_add
   · have hh: ((neighborsOf B.band (R+X.b) z).card:ℝ) ≤ weights X (R+X.b) := Nat.cast_le.mpr <| price_cover H.edge _ _
     refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (sq_nonneg g)) X.D_pos.le).trans_eq ?_; ring
   · refine le_trans (b:= dam X * threat B.loc z y (R+X.b+X.b)) ?_ ?_
     · rw [show dam X* _= X.D*(weights X X.b * threat B.loc z y (R+X.b+X.b)) from mul_assoc ..]
       exact mul_le_mul_of_nonneg_left (window_cost B.loc H.edge (nib y) (nib_nonneg y) ..) X.D_pos.le
     apply mul_le_mul_of_nonneg_left _ dam_pos.le
     let p:= neighborsOf B.loc R z; let v:= neighborsOf B.loc (R+X.b+X.b) z; let e:= weights X R; have h1:p ⊆ v:= enlarged B.loc z (show R ≤ R+X.b+X.b by omega)
     have h (p':Sky G ι) : ∑ i∈v\p,nib p' i+ threat B.loc z p' R=threat B.loc z p' (R+X.b+X.b):= (sum_sdiff h1 : ∑ i∈v\p,nib p' i+ _ = ∑ i∈v,nib p' i)
     have hE : ∑ i∈v\p,nib x i=∑ i∈v\p,nib y i:= sum_congr rfl fun i hi=> congr_arg (fun v=> G.chord v^2) (he _ (mem_sdiff.mp hi).2)
     have hx: threat B.loc z y R ≤ g^2*e := by
       refine (sum_le_sum hy).trans ?_; rw [sum_const,nsmul_eq_mul,mul_comm (g^2)]
       exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (price_cover H.core ..)) (sq_nonneg _)
     linarith only [hE,hx,h x,h y]
end Base

-- budget for g difference. stairs threshold > C*(Log g)^4, entropy ~(Log g)^5.
def incline (X:Prices):=1/(2*(dam X)^2)
lemma incline_pos : 0 < incline X:=by unfold incline; have h:=@dam_pos X; positivity
def rider (X:Prices): ℝ := X.D / dam X + X.D + dam X
lemma rider_pos : 0 < rider X:= by unfold rider; have := @dam_pos X; have := X.D_pos; positivity
namespace Base
include H
lemma charge {x y:Sky G ι} {z:Site S}{R:ℕ}{s t:T}(hs:0<B.choices s x)(ht:0<B.choices t y)
    (hy:∀ i∈neighborsOf B.loc R z,nib y i≤g^2)(he:∀ i∉neighborsOf B.loc R z, x i=y i)
    (hM:threat B.loc z x (R+X.b+X.b) ≤ (1+incline X)*threat B.loc z x R)
    (hc:∀ j∉neighborsOf B.band (R+X.b) z,B.cost s x j=B.cost t y j):
      threat B.loc z x R /(2*dam X) - rider X*g^2* weights X (R+X.b) ≤ B.action s x-B.action t y:=by
    let J:=neighborsOf B.band (R+X.b) z
    let I:= ∑ j∈J,B.cost s x j; let O:=∑ j∈J,B.cost t y j; let p:=weights X (R+X.b); let A:= threat B.loc z x R
    have hw:weights X R ≤ p:=weights_mono X (by omega : R ≤ R+X.b)
    have hd:0<dam X:=dam_pos; have h1:I-O=B.action s x-B.action t y:=by
        have h:B.action s x= I+ ∑ j∈univ \ J,B.cost s x j:=((add_comm ..).trans (sum_sdiff (subset_univ J))).symm
        have h₀:B.action t y= O+ ∑ j∈univ\J,B.cost t y j:= ((add_comm ..).trans (sum_sdiff (subset_univ J))).symm
        rw [h,h₀,sum_congr (s₁:=univ \ J) rfl (fun j hj=> hc j (mem_sdiff.mp hj).2),add_sub_add_right_eq_sub]
    rw [← h1]
    change threat _ _ _ _ ≤ (1+incline X)*A at hM
    have hF : O ≤ X.D*g^2*p+dam X*(g^2*p+incline X*A):=by
        refine (fill_price H ht hy he).trans ?_; change _+dam X*(_+_-A) ≤ _; rw [add_sub_assoc]
        gcongr; try linarith
    have hx: A - X.D*g^2*p ≤ I*dam X:=by rw [mul_comm I]; have ha:A ≤ _:= tax H x z R hs; change A≤ _ + _ * I at ha; nlinarith only [ha,mul_le_mul_of_nonneg_left hw (mul_nonneg X.D_pos.le (sq_nonneg g))]
    have hL: dam X*(incline X*A)= A /(2*dam X):= by unfold incline; field_simp
    have he₂:= (div_le_iff₀ hd).mpr hx
    rw [sub_div] at he₂
    rw [mul_add (dam X),hL] at hF
    change A/(2*dam X)- _ ≤ I-O
    unfold rider; rw [show _ *g^2 * weights X (R+X.b) = X.D*g^2*p/dam X + X.D*g^2*p + dam X * (g^2*p) from ?_]
    · have hi : A / dam X = 2*(A/(2*dam X)):=by field_simp
      linarith only [he₂,hF,hi]
    ring

lemma pair_stamp {x y:Sky G ι} (hg:0<g) {z:Site S}{R:ℕ}
    (hy:∀ i∈neighborsOf B.loc R z,nib y i≤g^2)(he:∀ i∉neighborsOf B.loc R z, x i=y i)
    (hM:threat B.loc z x (R+X.b+X.b) ≤ (1+incline X)*threat B.loc z x R):
    B.output g x ≤ Real.exp (rider X*weights X (R+X.b) - threat B.loc z x R /(2*dam X*g^2))*B.output g y:=by
    obtain ⟨M,hM',hr⟩:= H.glue z x y R he
    let v:= rider X * weights X (R+X.b)-threat B.loc z x R /(2*dam X*g^2)
    let d:=Real.exp v
    have ha s: B.choices s x*B.cash s g x ≤ ∑ t,M s t*(d*B.cash t g y):=by
       rw [show B.choices s x= _ from (hM'.west s).symm,sum_mul]
       refine sum_le_sum fun t _=> ?_; rcases (hM'.pos s t).eq_or_lt with hh|hh
       · rw [← hh,zero_mul,zero_mul]
       apply mul_le_mul_of_nonneg_left _ hh.le
       have hs : 0< B.choices s x:=(hh.trans_le (single_le_sum (fun i _ => hM'.pos s i) (mem_univ t))).trans_eq (hM'.west s)
       have ht : 0< B.choices t y:=(hh.trans_le (single_le_sum (fun i _ => hM'.pos i t) (mem_univ s))).trans_eq (hM'.east t)
       have hw:= charge H hs ht hy he hM (hr s t hh)
       unfold cash d; rw [← Real.exp_add,Real.exp_le_exp]; have hG:0<g^2:=by positivity
       rw [div_le_iff₀ hG, add_mul, div_mul_cancel₀ _ hG.ne', show v*g^2 = rider X*g^2*weights X (R+X.b) - threat B.loc z x R/(2*dam X) from ?_]; linarith only [hw]
       unfold v; have hx:=@dam_pos X; field_simp
    refine (sum_le_sum (fun i _=> ha i)).trans_eq ?_; rw [sum_comm,output,mul_sum]; refine sum_congr rfl (fun i _=>?_)
    rw [← sum_mul,show ∑ t, M t i=_ from hM'.east i]; change B.choices i y*(d* _) = d * (_ * _); ring
end Base
end YM.RGComparison.Core16.Forge

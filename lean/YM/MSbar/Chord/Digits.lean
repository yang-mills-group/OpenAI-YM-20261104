import YM.MSbar.Chord.Plane
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
local notation "M"=> Moment Q
variable (x:Edge (Site n)) (u v:G.Color) (h:Ribbon Q)(hQ:Weigh Q Z) (hu:‖u‖=1)(hv:‖v‖=1)
private lemma banjo (i:E): 1 ≤ beadPad x.1 i.1 1 := by simp [beadPad]
private lemma spur (p:S₀)(n m:ℕ): beadPad x.1 p (n*m)=(beadPad x.1 p n)^m:=by unfold beadPad; ring
private lemma earn (i j:Axis)(o:S₀)(p:ℝ)(hx:0≤p)(hp:∀ a,|zone x o a|≤p): |zone x o i *zone x o j ^2|≤p^3:=by rw [abs_mul,abs_pow]; refine (mul_le_mul (hp _) (pow_le_pow_left₀ (abs_nonneg _) (hp _) _) (pow_nonneg (abs_nonneg _) _) hx).trans_eq ?_; ring
include h hQ hu hv
-- gradient test cubic
lemma hueQuad (i:Axis) : |M x i u v [i,i]|≤ 30*tumbler n Z :=by
    let b(e:E):=beadPad x.1 e.1 1
    let f(y:S₀):= zone x y i^3
    let g(y:E):= if y.2=i then 3* middle x y i^2 +1/4 else 0
    have hh(y:E)(hp:sway f y-g y≠0) : n.val ≤ 100*(separation y.1 x.1+1) ∧ |sway f y-g y|≤ 13*beadPad x.1 y.1 3:=by
        let a:= b y; have hA:1≤ a:= banjo x y
        constructor
        · by_contra! he; apply hp; unfold sway f g; rw [sway_mid x y i he,zone_low x y i]; unfold halfE; by_cases he:y.2=i<;>simp [he,Ne.symm]<;>ring
        have h0:0 ≤ a:=zero_le_one.trans hA; apply (abs_sub ..).trans; have hz :|g y|≤4*a^3:=by
             unfold g; split; next ht=> rw [abs_of_nonneg (by positivity)]; rw [← sq_abs]; have hb := pow_le_pow_left₀ (abs_nonneg (middle x y i)) (medium_size x y i) 2; linarith only [show _ ≤ a^2 from hb,pow_le_pow_right₀ hA (by omega :2 ≤ 3),one_le_pow₀ hA (n:=3)]
             rw [abs_zero];positivity
        refine (add_le_add ((abs_sub ..).trans (add_le_add (show |f (y.1+step y.2)|≤ (2*a)^3 from ?_) (show |f y.1|≤a^3 from ?_))) hz).trans_eq ?_
        · unfold f; rw [abs_pow]; gcongr; exact sofB ..
        · unfold f; rw [abs_pow]; gcongr; exact sofa ..
        rw [show beadPad x.1 y.1 3=a^3 from spur x _ 1 3]; ring
    have ht := broad x u v h hQ hu hv (by norm_num: 0≤(13:ℝ)) hh; have he : ∑ a:E, cell Q x a u v*g a=3*M x i u v [i,i]+ M x i u v []/4:=by
        unfold Moment; rw [Finset.mul_sum,Finset.sum_div, ← Finset.sum_add_distrib,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; unfold g mold; simp; ring; exact fun j hj hu=> by simp [g,hu]
    rw [he] at ht
    have hf:= homeR x u v h hQ hu hv i; have hx:0 ≤ tumbler n Z:= by have :=(abs_nonneg _).trans hf; linarith
    obtain ⟨h0,h1⟩:=abs_le.mp hf; obtain ⟨h2,h3⟩:=abs_le.mp ht; rw [abs_le]; constructor<;> linarith only [h0,h1,h2,h3,hx]
lemma hueShift (i j:Axis)(he:i≠j):|M x i u v [j,j]+2*M x j u v [i,j]| ≤80*tumbler n Z :=by
    let f(y:S₀):= zone x y i*zone x y j^2
    let g(y:E):= (if y.2=i then middle x y j^2 else 0) + if y.2=j then 2*middle x y i*middle x y j else 0
    have hh(y:E)(hp:sway f y-g y≠0) : n.val ≤ 100*(separation y.1 x.1+1) ∧ |sway f y-g y|≤ 12*beadPad x.1 y.1 3:=by
        let a:=beadPad x.1 y.1 1; have hA:1≤a:=banjo x y; have h0:0 ≤ a:=zero_le_one.trans hA
        constructor
        · by_contra! hh; apply hp; unfold sway f g; rw [sway_mid x y i hh,zone_low x y i,sway_mid x y j hh,zone_low x y j]; unfold halfE; by_cases hi:y.2=i 
          · simp [hi,he, he.symm];ring
          by_cases hj:y.2=j
          · simp [hj,he,he.symm];ring
          simp [hi,hj,Ne.symm hi,Ne.symm hj]
        have hz :|g y| ≤ 3*a^3:=by
             have hp : |middle x y j^2|≤a^2:= by rw [abs_pow]; gcongr; exact medium_size ..
             have hi : |2*middle x y i*middle x y j| ≤ 2*a^2:=by rw [abs_mul,abs_mul,abs_of_pos zero_lt_two]; apply (mul_le_mul (mul_le_mul_of_nonneg_left (medium_size x y i) (by norm_num)) (medium_size x y j) (abs_nonneg _) (by unfold beadPad; positivity)).trans_eq; change 2*a*a=_; ring
             unfold g; have hk:a^2≤a^3:= pow_le_pow_right₀ hA (by omega); have hx:0 ≤ a^2:=sq_nonneg _; apply (abs_add_le ..).trans; refine (add_le_add (show |if y.2=i then middle x y j^2 else 0|≤a^2 from (by split; exact hp; simp [hx])) (show _≤2*a^2 from (by split; exact hi; simp; positivity))).trans ?_; linarith only [hk]
        rw [show beadPad x.1 y.1 3=a^3 from spur x _ 1 3]; apply (abs_sub ..).trans; have hi:= abs_sub (f (y.1+step y.2)) (f y.1); refine (add_le_add (hi.trans (add_le_add (earn x i j (y.1+step y.2) (2*a) (by positivity) (sofB x y)) (earn x i j y.1 a h0 (sofa x y.1)))) hz).trans_eq ?_; ring
    have ht:= broad x u v h hQ hu hv (B:=12) (by norm_num) hh; have hF : ∑ a:E, cell Q x a u v*g a= M x i u v [j,j]+2*M x j u v [i,j]:=by
        unfold Moment; rw [Finset.mul_sum,←Finset.sum_add_distrib,Fintype.sum_prod_type]; refine Finset.sum_congr rfl (fun y _=>?_); unfold g; simp [mul_add,mul_ite, Finset.sum_add_distrib,mold];ring
    rw [hF] at ht; have hn:= (abs_nonneg _).trans ht; linarith only [ht,hn]
end YM.MSbar.Midpoint

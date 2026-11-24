import YM.MS.Orbit.Slide
/-!
# Finite reading for inversion sectors. Project both field legs using Φ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Filter Function Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City
open scoped Topology ContDiff Interval
variable {A I: Type}{p:Sector A}
structure Cog (p:Sector A) where
    mode: A→A
    spin : A→ℂ
    vivid x: p (mode x)=p x
    perm : Involutive mode
    holo : ∀ x,spin x*spin (mode x)=1
namespace Cog
variable {F H:Raw A ℂ}(S:Cog p)
-- replace each mode x by u*x + v*spin(x)*rx
local notation "f"=> S.mode
local notation "r"=> S.spin
abbrev blend (u v:ℂ)(x:A): Op A ℂ:= u • (D x) + (v*r x) • (D (f x))
variable (u v:ℂ)
lemma blend_at (x:A): blend S u v x F=u • D x F+(v*r x) • (D (f x) F):= by rw [blend,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply]
def drive (u v:ℂ)(F: Raw A ℂ): Raw A ℂ | []=>F []| x::w=> drive u v (blend S u v x F) w
termination_by w=>w.length
-- S possibly should explicit in recursive line
lemma drive_rule (x:A) : D x (drive S u v F) = drive S u v (blend S u v x F):= by funext l; rw [at_D,drive]
lemma drive_add : drive S u v (F+H)=drive S u v F+drive S u v H:= by ext l; induction l generalizing F H with| nil=> simp [drive]| cons a l ih=> simp only [Pi.add_apply,D_eval a, drive_rule,map_add, ih]
lemma drive_smul (c:ℂ): drive S u v (c • F)=c • drive S u v F:= by ext l; induction l generalizing F with| nil=>simp [drive]| cons a l ih=> simp only [ Pi.smul_apply,D_eval a,drive_rule,map_smul,ih] -- rfl cases
abbrev wheel (u v:ℂ) : Op A ℂ:={
    toFun:=drive S u v
    map_add':= fun _ _=> drive_add S u v
    map_smul':= fun _ _=> drive_smul S u v _}
local notation "Φ"=> wheel S
@[simp] lemma wheel_nil (u v:ℂ): Φ u v F []=F []:= by unfold wheel; change drive S u v F []= _; rw [drive]
lemma wheel_rule (x): D x (Φ u v F)= Φ u v (blend S u v x F):= drive_rule ..
lemma roll_sign (b:Bool): wheel S u v ( Koszul.sign p b F )=Koszul.sign p b (wheel S u v F):= by
   have hc(x:A) (F: Raw A ℂ): blend S u v x ( Koszul.sign p b F )= (cross b (p x):ℂ) • Koszul.sign p b (blend S u v x F):= by simp_rw [blend_at, Koszul.sign_D, S.vivid,map_add,map_smul]; rw [smul_add]; rw [smul_comm u, smul_comm (v*r x)];
   funext l; induction l generalizing F with| nil=> simp only [ at_sign, degree_nil, cross_false', wheel_nil,one_mul ]| cons a l ih=> simp only [D_eval a, wheel_rule, hc,Koszul.sign_D,map_smul,Pi.smul_apply,ih] -- D_eval rewrites all
lemma rotate_p : Φ u v (Koszul.product p F H)= Koszul.product p (Φ u v F) (Φ u v H):= by
   have ht(x:A)(F H:Raw A ℂ): blend S u v x ( product p F H )= product p ( blend S u v x F) H+product p (sign p (p x) F) ( blend S u v x H ):= by simp only [D_product,S.vivid,map_add,map_smul,LinearMap.smul_apply, LinearMap.add_apply, smul_add]; abel
   funext l; induction l generalizing F H with| nil=> simp only [wheel_nil]; rw [show product p F H [] = F []*H [] from times_nil .., show product p _ _ [] = _ from times_nil ..]; simp only [wheel_nil]| cons a l ih=> simp only [D_eval a,D_product,wheel_rule,← roll_sign, ht,map_add,Pi.add_apply, ih ]
lemma merged (c d:ℂ)(F:Raw A ℂ): Φ u v (Φ c d F)=Φ (u*c+v*d) (u*d+v*c) F:= by
   have hx(x:A)(F:Raw A ℂ): blend S u v x (Φ c d F)= Φ c d (blend S (u*c+v*d) (u*d+v*c) x F):= by
      simp only [ blend_at,wheel_rule S, ← map_smul, ← map_add ]; apply congr_arg; simp only [show S.mode (S.mode x)=x from S.perm x,map_smul]; funext l; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; linear_combination (norm:=ring_nf) v*d*( D x F l )*( S.holo x )
   funext l; induction l generalizing F with| nil=>simp only [wheel_nil]| cons a l ih=> simp only [ D_eval a, wheel_rule, hx, ih]
lemma alone (F:Raw A ℂ): Φ 1 0 F=F:= by funext l; induction l generalizing F with | nil=> simp | cons a l ih=> rw [D_eval a (Φ 1 0 F),wheel_rule]; simp only [blend_at, zero_mul, one_smul,zero_smul,add_zero,ih, at_D ]
abbrev look := Φ ((2:ℂ)⁻¹) ((2:ℂ)⁻¹)
abbrev mirror := Φ 0 1
abbrev Invar (F:Raw A ℂ): Prop:= mirror S F=F
lemma merge_mm : S.mirror (S.mirror F)=F:= by rw [ mirror, merged ]; simp only [zero_mul,mul_zero, one_mul, zero_add]; exact alone ..
lemma look_read : S.look (S.look F)=S.look F:= by unfold look; rw [merged S]; norm_num
lemma takeover : S.look (S.mirror F)=S.look F:= by unfold look mirror; rw [merged S]; simp only [mul_zero,mul_one,zero_add,add_zero]
lemma heal : S.mirror (S.look F)= S.look F:= by unfold look mirror; rw [merged]; simp only [zero_mul, one_mul, zero_add]
lemma reflect (x:A): D x (S.mirror F)= r x • S.mirror ( D (f x) F):= by unfold mirror; rw [wheel_rule,blend_at]; simp
lemma view (x:A): D x (S.look F)= ((2:ℂ)⁻¹) • (S.look (D x F)+ r x • S.look (D (f x) F)):= by unfold look; rw [wheel_rule,blend_at,map_add,map_smul,map_smul]; rw [smul_add,mul_smul]
lemma slide (h:S.Invar F)(x:A): S.look (D x F)= r x • S.look ( D (f x) F ):= by nth_rw 1 [← h]; rw [reflect,map_smul,takeover]
end Cog
end YM.MS.Orbit

import YM.MSbar.Grass.Braids

/-! Master compatibility relations on homogenous kernels. (No incidence groups yet.)
Spell out differential identities for zero-, one-, two-loop outputs with commuting operators.
Missing dynamic calls not hidden in inputs later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset
open scoped BigOperators Classical
variable {T:Type*}{p:T→Bit} {f g h : Series T} {d e r k j : Bit}
variable {P D:Stock T}
local notation:80 a:80 " □ " b:81 => join p a b
local notation "pa" => pairs p 0 P
local notation "da" => pairs p 0 D
local notation "A" => laps P
local notation "B" => laps D
lemma Homogeneous.cm (hf:Homogeneous p 0 f)(hg:Homogeneous p e g): g □ f=f □ g:=by rw [atom_clean hg hf,sign_zero,one_smul]
lemma Homogeneous.z (hf:Homogeneous p 0 f): Homogeneous p 0 (f □ f):=by simpa only [add_zero] using hf.join hf
namespace Grade
section
variable (hp: Grade p k P)
variable (hf:Homogeneous p 0 f)
include hp hf
lemma first (g): A (f □ g)=A f □ g+ f □ (A g)+ pa f g:=by rw [hp.product hf, sign_zero,one_smul]
lemma symmetric (hg:Homogeneous p e g): pairs p e P g f=pa f g:=by rw [hp.swap hg hf,sign_zero,one_smul]
lemma double : A (f □ f)=(2:ℂ) • (f □ (A f))+ pa f f := by rw [hp.first hf, hf.cm (hp.homogeneous hf), two_smul]
lemma pair_sq (hg:Homogeneous p d g) : pa (f □ f) g=(2:ℂ) • (f □ (pa f g)):=by
    rw [← hp.symmetric hf.z hg,hp.derivation hg hf hf,sign_zero,one_smul,hf.cm (hp.loss hg hf),hp.symmetric hf hg,two_smul]
lemma cube : A (f □ (f □ f))=(3:ℂ) • (f □ (f □ A f))+(3:ℂ) • (f □ (pa f f)):=by
   rw [hp.first hf, hp.double hf, hp.symmetric hf.z hf -- symmetric uses f □ f as unit?
       ,hp.pair_sq hf hf,hf.z.cm (hp.homogeneous hf),join_assoc hf hf (hp.homogeneous hf), join_add_right,join_scale_right]
   funext w; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
end

section
variable (hp:Grade p 0 P) (hD:Grade p k D)
include hp hD
lemma linear (hf:Homogeneous p d f): A (B f)= B (A f):=by rw [hD.id_loop hp hf,sign_zero_left,one_smul]
local notation "R" => pa f f
local notation "S" => da f f
variable (hf: Homogeneous p 0 f)
include hf
lemma quadratic : A S+(2:ℂ) • pa f (B f)= B R + (2:ℂ) • da f (A f):= by
    have he:= hp.linear hD hf.z
    simp_rw [hD.double hf,hp.double hf,map_add,map_smul,hp.first hf,hD.first hf,hp.linear hD hf] at he
    have ha:Homogeneous p 0 (A f):=by simpa only [add_zero] using hp.homogeneous hf
    rw [ha.cm (hD.homogeneous hf)] at he
    funext v; replace he := congr_fun he v; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at he ⊢; linear_combination he
lemma cubic : pa f S= da f R := by
    have he:= hp.linear hD (by simpa using hf.join hf.z : Homogeneous p 0 (f □ (f □ f)))
    -- prefer derivative pairing f^2
    have ha:Homogeneous p 0 (A f):=by simpa only [add_zero] using hp.homogeneous hf
    have hd:= hD.homogeneous hf; have hs:= hD.loss hf hf; have hr:Homogeneous p 0 R := by simpa only [add_zero] using hp.loss hf hf
    have eh:= hp.quadratic hD hf
    have e' := congr_arg (join p f) eh; simp_rw [join_add_right,join_scale_right] at e'
    rw [hp.cube hf,hD.cube hf, ← join_assoc hf hf hd,← join_assoc hf hf ha] at he
    simp_rw [map_add,map_smul,hp.first hf.z,hD.first hf.z,hp.first hf,hD.first hf] at he
    rw [hp.pair_sq hf hd,hD.pair_sq hf ha,hf.cm ha,hf.cm hd,hp.linear hD hf] at he
    simp_rw [join_add_left] at he
    rw [hr.cm hd,ha.cm hs -- pattern Df? inspect
       ] at he
    simp_rw [join_assoc hf ha hd,join_assoc hf hd ha,ha.cm hd] at he
    funext v; have H:=congr_fun e' v; replace he:=congr_fun he v; simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul] at *; linear_combination (he - 3*H)/3
end
end Grade
end YM.MSbar.Super

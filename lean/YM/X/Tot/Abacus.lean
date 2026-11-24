import YM.X.Tot.Trill
/-!
# Only distributional singlets in remaining vertex integral.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open Crate Clove Braid Reed PertExtension Hinge
open Stems hiding X
open Fielding
open scoped Topology ContDiff BigOperators Classical
variable {V W I:Type*}
local notation "P"=>poly V
variable (q:Symmetric V)(A B C' U:poly V) (x y z:V→₀ℂ)
local notation "κ"=> knot q
local notation "∂"=> Braid.edge q
abbrev triple (x y z:V→₀ℂ): Normal.poly V:= glyph x*(glyph y*glyph z)
local notation "E"=> tri q
def send (x y z:V→₀ℂ):ℂ:= E (∂ x A) (∂ y B) (∂ z C')
def scrim (x y z:V→₀ℂ):ℂ:= E (∂ z (∂ y A)) (∂ x B) C'+ E (∂ z (∂ y A)) B (∂ x C')
lemma calc_major : majority q (triple x y z) A B C'= scrim q A B C' x y z + scrim q A B C' y x z + scrim q A B C' z x y + E (∂ z (∂ y (∂ x A))) B C':= by
    rw [majority,triple,m3]; simp only [tri_plus,tri_cross,scrim]
lemma expand_one : space q A B C' (glyph x)=E (∂ x A) B C' + E A (∂ x B) C'+E A B (∂ x C'):= by nth_rw 1 [←mul_one (glyph x)]; rw [quad_cross]
lemma just_school : school q A B C' (triple x y z) = send q A B C' x y z+send q A B C' x z y+send q A B C' y x z+send q A B C' y z x + send q A B C' z x y+send q A B C' z y x:= by
    rw [school]; simp only [calc_major,scrim,send,triple, quad_cross ,expand_one,tri_C,tri_S]; ring
-- reindex aliases
variable (f:V→W)(Q:Symmetric W)(he:q=remap f Q)
local notation "Xv"=>rename (R:=ℂ) f
include he
lemma turn_mix : Xv (multi q A U)=multi Q (Xv A) (Xv U):= by
     subst q; let q:= remap f Q; have h : remap f (-Q)=-q:= Normal.Symmetric.ext (funext (fun i=>funext fun j=> by rw [remap_cov]; exact congr_arg (- ·) (remap_cov f Q i j).symm));
     have hd: ∀ (i:V), slit (Q.cov (f i)) (rename f A)= rename f (slit (q.cov i) A):= fun i=> by rw [YM.PositionX.Rank.slit_rename,show Q.cov _ ∘ f = q.cov i from funext (fun j=> (remap_cov ..).symm)] -- names
     have hh: Xv (hit q A U)= hit Q (Xv A) (Xv U):= by
        induction U using MvPolynomial.induction_on with| C u=> simp_rw [hit_c,rename_C,map_zero,hit_c] | add u v hu hv=> simp_rw [map_add,hu,hv]| mul_X U i IH=> rw [(hit _ _).leibniz, map_mul Xv,(hit Q _).leibniz]; simp only [smul_eq_mul,map_add,map_mul,IH,rename_X,hit_point,hd]
     change (Xv) (multi q _ _) = _; unfold multi knot; simp_rw [map_sub,map_mul,hh]; rw [renative f (-Q), renative f (-Q), ← map_mul (f:=Xv) (milk (remap f (-Q)) A), renative,h]; -- h orientation? fix
lemma perp : space q A B C' U= space Q (Xv A) (Xv B) (Xv C') (Xv U):= by
    rw [market,market]; change shock q _= shock Q _; rw [he, remaps]; have hx: remap f (-Q)=- remap f Q:= Normal.Symmetric.ext (funext fun i=> funext fun j=> by rw [remap_cov]; exact congr_arg (- ·) (remap_cov f Q i j).symm); simp_rw [map_mul,renative,hx]
lemma triple_sym : tri q A B C'= tri Q (Xv A) (Xv B) (Xv C'):= by unfold tri; rw [perp _ A _ _ 1 f Q he,map_one]
lemma hex : majority q U A B C'= majority Q (Xv U) (Xv A) (Xv B) (Xv C'):= by unfold majority;rw [triple_sym _ _ _ _ f Q he, turn_mix _ _ _ f Q he]
end YM.PositionX.Tot

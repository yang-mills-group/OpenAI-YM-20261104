import YM.X.Tot.Knell
/-!
# algebra of interaction with one cubic insertion. Use independent alphabets or same alphabet with Symmetric. At already Wick-corrected columns (relative milk). Majority term exact all At(Taylor weight), classical comp etc. Symmetry of argument needed integrals and low-moment cost.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open Crate Clove Braid Reed PertExtension
open Stems hiding X
open Fielding
open scoped Topology ContDiff BigOperators Classical
variable {V W I:Type*}
local notation "P"=>poly V
variable (q: Symmetric V) (A B C' U:poly V) (x y z:V→₀ℂ)
local notation "κ"=> knot q
def pipe(v w u :P): P:=κ v (κ w u)
abbrev eye(V:Type*) := (MvPolynomial.aeval (R:=ℂ) (0:V→ℂ)).toLinearMap
def space(A B C X : P):ℂ:= eye V (κ X (pipe q A B C))
abbrev tri(A B C:P):= space q A B C 1
lemma tri0 : tri q A B C'=eye V (pipe q A B C'):= by rw [tri,space,pone]
lemma market : space q A B C' U=Next.Rank.Normal.blend q 0 (milk (-q) U * milk (-q) A*milk (-q) B*milk (-q) C'):= by rw [space,pipe,blend_components]; unfold knot; simp_rw [minus]; simp_rw [mul_assoc]; rfl
lemma space_S : space q A B C' U=space q B A C' U:= by rw [market,market]; apply congr_arg (Next.Rank.Normal.blend q 0); ring
lemma space_C : space q A B C' U=space q A C' B U:= by rw [market,market]; apply congr_arg (Next.Rank.Normal.blend q 0); ring
lemma space_X : space q A B C' U=space q U B C' A:= by rw [market,market, mul_comm (milk (-q) U)]
lemma tri_S : tri q A B C'=tri q B A C':= space_S ..
lemma tri_C : tri q A B C'=tri q A C' B:= space_C ..
lemma tri_rotate : tri q A B C'=tri q C' A B:= by rw [tri_C q A,tri_S q A]
lemma tri_spin : tri q A B C'=tri q B C' A:= Eq.symm (tri_rotate ..)
-- use bundled quad ℂ via ∗simp*; repeated multilinear.mk₂? (poly etc). Could avoid.
def armQ (A B C:P):P→ₗ[ℂ]ℂ:= eye V ∘ₗ (oral q).flip (pipe q A B C)
lemma into :space q A B C' U=armQ q A B C' U:=rfl
lemma space_add (p:P): space q A B C' (U+p)=space q A B C' U+space q A B C' p:= map_add (armQ q A B C') U p
lemma space_scale (a:ℂ) : space q A B C' (a • U)=a • space q A B C' U:= map_smul (armQ q A B C') a U
lemma qu_zero : space q A B C' 0=0:=map_zero (armQ q A B C')
lemma tri_plus (p:P): tri q (A+p) B C'= tri q A B C' + tri q p B C':= by unfold tri; rw [space_X,space_add,space_X q A,space_X q p]
lemma tri_sum {I:Type*} (F:I→P)(l:Finset I): tri q (∑ i∈l,F i) B C'= ∑ i∈l, tri q (F i) B C':= by unfold tri; simp_rw [space_X (q:=q) (B:=B) (U:=1), into];exact map_sum (armQ q 1 B C') ..
lemma tri_scale (a:ℂ): tri q (a • A) B C'=a • tri q A B C':= by unfold tri; rw [space_X,space_scale,space_X q A]
lemma tri_plus₁(p:P): tri q A (B+p) C'= tri q A B C' + tri q A p C':= by rw [tri_S q A, tri_plus, tri_S q A,tri_S q A]
lemma tri_plus₂(p:P): tri q A B (C'+p)=tri q A B C'+tri q A B p:= by rw [tri_rotate q A,tri_plus,tri_rotate q A,tri_rotate q A]
lemma tri_scale₁(a:ℂ):tri q A (a • B) C'= a • tri q A B C':= by rw [tri_S q A, tri_scale,tri_S q A]
lemma tri_scale₂(a:ℂ):tri q A B (a • C')= a • tri q A B C':=by rw [tri_C q A, tri_scale₁,tri_C q A]
lemma tri_sum₁{I:Type*}(F:I→P)(l:Finset I):tri q A (∑ i∈l,F i) C'=∑ i∈l,tri q A (F i) C':= by simp_rw [tri_S q A]; rw [tri_sum]
lemma tri_sum₂{I:Type*}(F:I→P)(l:Finset I):tri q A B (∑ i∈l,F i)=∑ i∈l,tri q A B (F i):= by simp_rw [tri_rotate (q:=q) (A:=A) (B:=B)]; rw [tri_sum]
@[simp] lemma tri_z:tri q 0 B C'=0:= by rw [tri0,pipe,pzero,map_zero]
@[simp] lemma tri_z₁:tri q A 0 C'=0:= by rw [tri_S q A,tri_z]
@[simp] lemma tri_z₂:tri q A B 0=0:= by rw [tri_rotate,tri_z]
/-- derivative travels through a free mode arrow (vertex jump) -/
local notation "∂"=> Braid.edge q
lemma quad_cross : space q A B C' (glyph x * U) = space q (∂ x A) B C' U+ space q A (∂ x B) C' U+ space q A B (∂ x C') U:= by
    rw [space,pstep]; simp only [pipe,space,edge,skimmers,padd,padd',map_add]; let f:= eye V; have he(p:P):f (glyph x *p)=0:= by change aeval (0:V→ℂ) _=_; rw [_root_.map_mul,Crate.aeval_glyph,zero_mul]; -- name
    simp_rw [show ∀p:P, (eye V) (glyph x *p) = _ from he]; ring
lemma tri_cross : tri q (glyph x*A) B C' = tri q A (∂ x B) C'+tri q A B (∂ x C'):= by
   unfold tri; rw [space_X,quad_cross,Derivation.map_one_eq_zero,space_X q 0]; rw [show space q A B C' 0=0 from qu_zero ..,zero_add]; simp_rw [space_X (q:=q) (U:=1) (A:=A)]
def majority (q: Symmetric V) (U A B C:P):= tri q (multi q A U) B C
def school (A B C U:P):ℂ:= space q A B C U -majority q U A B C - majority q U B A C -majority q U C A B
lemma expand_X : space q A B C' U= school q A B C' U+majority q U A B C'+majority q U B A C'+majority q U C' A B := by unfold school; ring
lemma majority_sym : majority q U A B C'=majority q U A C' B:= tri_C .. -- second & third
lemma school_sym : school q A B C' U= school q B A C' U:= by unfold school; rw [space_S q A,majority_sym q (U:=U) C']; ring
lemma school₁ : school q A B C' U= school q A C' B U:= by unfold school; rw [space_C q A, majority_sym q (U:=U) A]; ring
-- explicit formula
end YM.PositionX.Tot

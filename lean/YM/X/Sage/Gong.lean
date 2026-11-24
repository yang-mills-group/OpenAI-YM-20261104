import YM.X.Sage.Hammer
/-!
# six chiral components orth identity and the topological derivative sign. Used rational matrices uppercase.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V:Type*} {q:ℕ+} {r R:ℝ}
local notation "L"=> (atTop:Filter ℕ)
local notation "U"=> G.ColorIndex
local notation "θ"=> Reed.Horizontal G
local notation "Θ"=> (⊤:Submodule ℝ (Fan G))
local notation "T"=> Tet
local notation "A"=>PlaqAxes
abbrev plaq (i j:Axis)(h:i<j:= by decide) : PlaqAxes:= ⟨(i,j),h⟩
-- enumerate
private lemma status_next (i j a b:Axis) (h:i≠a ∨j≠b) (p:i < j) (q:a < b): plaq i j p≠plaq a b q:= fun hh=> h.elim (fun h=> h (congr_arg (fun i:PlaqAxes=>i.val.1) hh)) (fun h=> h (congr_arg (fun i:PlaqAxes=> i.val.2) hh))
lemma finsum [AddCommMonoid V](f:PlaqAxes→V): ∑ i:PlaqAxes,f i=f (plaq 0 1)+f (plaq 0 2)+f (plaq 0 3)+f (plaq 1 2)+f (plaq 1 3)+f (plaq 2 3):= by
    have he: (Finset.univ (α:=PlaqAxes))={plaq 0 1,plaq 0 2,plaq 0 3,plaq 1 2,plaq 1 3,plaq 2 3}:= by decide
    rw [he]; repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]; ac_rfl -- simp won't choose i!
section ring
variable [CommRing V] [Algebra ℂ V] (f g h: A→ V)
def projectF (r:ℝ)(f:A→V)(i:T):= ∑ v:A,(↑(dataF r i v):ℂ) • f v
lemma psi₀(t:ℝ): projectF t f 0=f (plaq 0 1)+(t:ℂ) • f (plaq 2 3):= by simp only [projectF,finsum]; norm_num [dataF,form,plaq]
lemma psi₁(t:ℝ): projectF t f 1=f (plaq 0 2)-(t:ℂ) • f (plaq 1 3):= by simp only [projectF,finsum]; norm_num [dataF,form,plaq, sub_eq_add_neg]
lemma psi₂(t:ℝ): projectF t f 2=f (plaq 0 3)+(t:ℂ) • f (plaq 1 2):= by simp only [projectF,finsum]; norm_num [dataF,form,plaq]
lemma difference : ∑ i:A,f i*g i=(∑ p:T,projectF (-1) f p*projectF (-1) g p)+f (plaq 0 1)*g (plaq 2 3)+f (plaq 2 3)*g (plaq 0 1)-f (plaq 0 2)*g (plaq 1 3)-f (plaq 1 3)*g (plaq 0 2)+f (plaq 0 3)*g (plaq 1 2)+f (plaq 1 2)*g (plaq 0 3):= by simp_rw [finsum, sum3,psi₀,psi₁,psi₂]; push_cast; rw [neg_one_smul,neg_one_smul,neg_one_smul,neg_one_smul,neg_one_smul,neg_one_smul]; ring
end ring
local notation "P"=> Curly G
variable (a:G.ColorIndex)
local notation "D"=> dialF (G:=G)
def W_g (v:PlaqAxes)(a:G.ColorIndex) := glove (v,a)
lemma F_axial (p:T)(r:ℝ): projectF r (fun v:A=>faceText v a) p= D (Emitter r p a):= by unfold projectF Emitter; simp_rw [map_sum,map_smul,dialF, exchange_x,Function.comp_apply, com_text];rfl
lemma G_axial (p:T)(r:ℝ): projectF r (fun v:A=> W_g v a) p= call D glove (Emitter r p a):= by unfold projectF Emitter; simp_rw [map_sum,map_smul,call_X];rfl
abbrev classic (G:Gauge): Curly G := ∑ v:A, classicV v
def minus_vertex (G:Gauge): Curly G:= ∑ a:G.ColorIndex,∑ p:Tet,dialF (Emitter (-1) p a)*call dialF glove (Emitter (-1) p a)
def wedge (v w:A):P:= ∑ a:U,faceText v a*glove (w,a)
def weave (G:Gauge):Curly G := wedge (plaq 0 1) (plaq 2 3)+ wedge (plaq 2 3) (plaq 0 1) - wedge (plaq 0 2) (plaq 1 3)-wedge (plaq 1 3) (plaq 0 2)+wedge (plaq 0 3) (plaq 1 2)+wedge (plaq 1 2) (plaq 0 3)
lemma chorus : classic G=minus_vertex G+weave G:= by
    unfold classic classicV; rw [Finset.sum_comm]; unfold minus_vertex weave wedge; simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; let f(v:A):= faceText v i; let g(v:A):=W_g v i; have he := difference f g; simp_rw [show ∀(v:T),projectF (-1) f v= _ from fun v=>F_axial i v (-1), show ∀v:T,projectF (-1) g v= _ from fun v=> G_axial i v (-1)] at he; unfold f g W_g at he; rw [he]; abel
end YM.PositionX.Sage

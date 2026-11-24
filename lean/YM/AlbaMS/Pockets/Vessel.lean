import YM.AlbaMS.Pockets.Sparse
import YM.AlbaMS.Super.Shoe

/-!
Radius at depth. bounded formal perturbative masks. From separate real Coils
(to feed finite or covering lattice) maintain reconstruction Receipt.
Coefficients read multiplicatively, truncation via `Tags`, not assuming
field polynomials in the actual continuum perturbation hierarchy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open Coil
open scoped BigOperators Classical
variable {ι K W R : Type*} [Fintype K] [AddCommMonoid W] [CommRing R]
namespace Ladder
variable {D : Ladder K W} {ρ : ι→ Bool}
variable {F G H : Coil ρ R} {U V:Coil ρ (Tags D R)} {f : K→Coil ρ R} {p : Bool} {x : K} {a b m n : ℕ} {v : Finset ι}

def rail (D : Ladder K W)(g : ι→ι→R): ι→ι→Tags D R:= fun i j=> Tags.inject D (g i j)
def clip (D : Ladder K W)(x:K): Coil ρ (Tags D R)→+ Coil ρ R:= seep (Tags.peek x)
def poke (D : Ladder K W)(x:K): Coil ρ R→+ Coil ρ (Tags D R):= seep (Tags.pixel D x)
def load (D : Ladder K W)(f:K→Coil ρ R): Coil ρ (Tags D R):= ∑ x : K,poke D x (f x)
@[simp] lemma clips {l}: clip D x U l=U l x:=rfl
lemma poked {l}: poke D x F l=Tags.gem D x (F l):=rfl
lemma ext_rail (h:∀ x,clip D x U=clip D x V): U=V:=Coil.ext _ _ fun l=>Tags.same _ _ fun i=> DFunLike.congr_fun (h i) l
lemma peek_poke (F : Coil ρ R)(x y : K):clip D x (poke D y F)=if x=y then F else 0:=by ext l;by_cases he:x=y<;>simp [poked,Tags.gem_read,he,Ne.symm]
lemma loads :clip D x (load D f)=f x:=by unfold load; rw [map_sum]; simp [peek_poke]
lemma reload : U= load D (fun x=> clip D x U):= ext_rail fun _=> by rw [loads]
lemma clip_scale (c:R):clip D x (Tags.inject D c • U)=c • clip D x U:= seep_smul U _ _ _ fun _=>Tags.mult_read ..
lemma clip_rank : clip D x (rankn n U) = rankn n (clip D x U):=by ext l; rw [rankn_read,clips,rankn_read]; split<;> rfl
lemma total_cap (h:∀ i,Cap (f i) m): Cap (load D f) m:=Cap.sum _ _ (fun i _=> Cap.seep _ _ (h i))
variable {g : ι→ι→R}
lemma clips_prod : clip D x (U*V) = ∑ y∈ D.sums x, clip D y.1 U * clip D y.2 V:=
    seep_many _ _ _ (D.sums x) (fun y=> Tags.peek y.1) (fun y=> Tags.peek y.2) (fun c d=>Tags.product_cell c d x)
lemma lines (h:Graded ρ p g):Graded ρ p (D.rail g):= fun i j he=> h i j (fun hv=> he (by simp [rail,hv]))
lemma clip_touch : clip D x (touch (D.rail g) v U)=touch g v (clip D x U):=seep_touch U _ fun _ _ c=> Tags.mult_read c x _
lemma clip_cross (h:Graded ρ p g): clip D x (cross p (D.rail g) v U V)=∑ y∈ D.sums x,cross p g v (clip D y.1 U) (clip D y.2 V):=
    seep_many_cross (s:=v) p U V _ (D.sums x) (fun a=> Tags.peek a.1) (fun a=> Tags.peek a.2) (fun c d=> Tags.product_cell c d x) (lines h) h (fun _ _ c=>Tags.mult_read c x _)

def fuel (D : Ladder K W) : ℕ:= ∑ i:K,D.d i
lemma d_le : D.d x≤ D.fuel:= Finset.single_le_sum (f:=D.d) (fun _ _=> Nat.zero_le _) (Finset.mem_univ _)
def Silent (D : Ladder K W)(n : ℕ)(F : Coil ρ (Tags D R)):=∀ i, D.d i < n → clip D i F=0
namespace Silent
lemma mono (h:Silent D n U)(H:m≤n): Silent D m U:=fun i hi=> h i (hi.trans_le H)
lemma empty (h:Silent D n U)(H:D.fuel<n): U=0:= ext_rail fun i=> (h i (lt_of_le_of_lt d_le H)).trans (map_zero _).symm
lemma mul (h:Silent D a U)(H:Silent D b V): Silent D (a+b) (U*V):=by
  intro x hx; rw [clips_prod]; refine Finset.sum_eq_zero fun y hy=>?_ ; have hy' := D.raises' ((D.member ..).1 hy)
  by_cases he: D.d y.1 < a; rw [h y.1 he,zero_mul];rw [H y.2 (by omega),mul_zero]
lemma pow {n} (h:Silent D 1 U): Silent D n (U^n):=by
  induction n with|zero=>exact fun _ ht=> by omega|succ n ih=>rw [pow_succ];exact ih.mul h
lemma nil (h:clip D D.ort U=0): IsNilpotent U:= by
  have H:Silent D 1 U:=fun i hi=>by by_cases hu:i=D.ort; simpa [hu]; exact False.elim (Nat.not_lt.2 (D.lift hu) hi)
  exact ⟨D.fuel+1,H.pow.empty (Nat.lt_succ_self _)⟩
end Silent
end Ladder
end YM.MSBar.Bric

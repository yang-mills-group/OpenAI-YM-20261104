import YM.QuadraticLocal.Sunrise.Picture
/-!
# Rank built from slips, finite-linear only
All the corresponding impulses.A.C.E. of `Focus.Lens` excel projector accounted; here prove
 ANY rank polynomial expands into finite linear combos of slips preserving degree.Limits.
 Apply later to α (≤κ) at ALL bounded regulator & witnesses; no meas.Lattice rates required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Focus
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module Push AllOrder.Ink.Money
open scoped BigOperators Topology Classical ContDiff
variable {n:Side} {α ι : Type}[Fintype α][Fintype ι][DecidableEq ι]
local notation "U"=> rule α n
local notation "K"=> Leaf n α
variable {a C D:ℝ} {k:ℕ}
inductive Floss (α:Type) (n:Side) (k:ℕ) : (rule α n→ℝ)→Prop
 | single (S:Slip (Leaf n α))(he:S.length≤k): Floss α n k (fun u=> paid u S)
 | plus {f g:rule α n→ℝ}: Floss α n k f → Floss α n k g → Floss α n k (f+g)
 | scale (c:ℝ){f:rule α n→ℝ}: Floss α n k f → Floss α n k (c•f)
namespace Floss
variable {f g:rule α n→ℝ}
lemma constant (k:ℕ)(w:ℝ): Floss α n k (fun _=>w):= by convert (scale w (single (n:=n) (α:=α) (k:=k) [] (Nat.zero_le _))) using 1; ext1 i; exact (mul_one _).symm
lemma mass {I:Type*}(S:Finset I)(u:I→U→ℝ)(h:∀ i∈S,Floss α n k (u i)):Floss α n k (∑ i∈S,u i) := by
 induction S using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact constant k 0
 | insert i j hi ih=> rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma song (h:Floss α n k f)(i:Leaf n α) : Floss α n (k+1) ((fun x:U=> x i)*f):= by induction h with
 | single L h=> exact single (i::L) (Nat.add_le_add_right h _)
 | plus _ _ h h' => rw [mul_add]; exact h.plus h'
 | scale m _ h => rw [mul_smul_comm]; exact h.scale m
lemma realm (f:U→ℝ)(h:Rank U k f) : Floss α n k f:= by
 induction h with
 | nil k c=> apply constant
 | add _ _ h h' => exact h.plus h'
 | @dot p m f h ih=>
    rw [show ⇑p = ∑ i:Leaf n α,p (spot i) • (fun x:U => x i) from ?_, Finset.sum_mul]; swap;
    · funext y; rw (occs:=.pos [1]) [← Push.Uniform.combine y]; rw [_root_.map_sum,Finset.sum_apply]; refine Finset.sum_congr rfl (fun i _=>?_); rw [_root_.map_smul]; exact mul_comm (y i) _
    apply mass; intro i _; rw [smul_mul_assoc]; exact (ih.song i).scale (p _)
lemma prefect (h:Floss α n k f): Rank U k f:= by induction h with
 | single L h=> exact ((Field.frame_cost L).2.1.up h)
 | plus _ _ h h'=> exact h.add h'
 | scale r _ h=> exact h.scal _
end Floss
end YM.QuadraticLocal.Sunrise.Focus

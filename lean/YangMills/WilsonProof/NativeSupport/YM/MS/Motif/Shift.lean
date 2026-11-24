import YM.MS.Motif.Shift
import YM.MS.Motif.Vox
/-!
# Constructor for finite polynomial coupling vectors

Equalities by coefficients in dense T when emitted. Allow case coefficient fully absent. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif.Literal
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native Book Convolve Signal
open scoped Topology ContDiff Interval
variable {I E F A :Type}[AddCommGroup E][Module ℂ E][AddCommGroup F][ Module ℂ F]
  [AddCommGroup I][Module ℂ I]

-- coefficient at n
variable {X:Box E}{L:E→ₗ[ℂ] F→ₗ[ℂ] I}
lemma whole (L:E→ₗ[ℂ] F)(X:Box E) (n:ℕ): linear F (Boom 0 L X) n=L ( X n ) := by
    rw [ ← Finsupp.sum_single X ]; -- occurrence both OK
    simp only [Finsupp.sum,map_sum,Boom_sl, Nat.zero_add,hiss,Finset.sum_apply',Finsupp.single_apply,map_zero, apply_ite]; -- probe
lemma seatpair (L:E→ₗ[ℂ] F→ₗ[ℂ] I)(x:E)(y:F)(m n k:ℕ) : (root L (Finsupp.single m x) (Finsupp.single n y)) k= pairW L ( linear E ( Finsupp.single m x)) (linear F (Finsupp.single n y)) k:= by
    rw [root_sl,Boom_sl,Finsupp.single_apply,paired]; split <;> rename_i h; · rw [Finset.sum_eq_single (m,n)]; simp [hiss]; intro j hj ht; obtain ⟨a,b⟩:=j; obtain hs:= Finset.mem_antidiagonal.mp hj; have ht:a≠m:= (by simp_all; omega); simp [hiss, Ne.symm ht]; exact fun x=> (x (Finset.mem_antidiagonal.mpr h)).elim
    symm; apply Finset.sum_eq_zero; intro j hj; obtain he:=Finset.mem_antidiagonal.mp hj; by_cases hz:j.2=n; simp [hiss, show m≠j.1 by omega]; simp [hiss,Ne.symm hz]
lemma pair_real (L:E→ₗ[ℂ] F→ₗ[ℂ] I)(U:Box E)(V:Box F): linear I (root L U V)= pairW L (linear E U) (linear F V):= by
   rw [← Finsupp.sum_single U, ← Finsupp.sum_single V]; simp only [Finsupp.sum,map_sum,LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=>funext fun p=> seatpair L _ _ _ _ p
end YM.MS.Motif.Literal

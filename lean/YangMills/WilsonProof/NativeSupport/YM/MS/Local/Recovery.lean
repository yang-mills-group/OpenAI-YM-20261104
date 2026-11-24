import YM.MS.Local.Recovery
import YM.MS.Local.Normal
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Realizing the letter matrices with point readout, for all positions.

Finite dimensional argument over the coefficient field (here complex). Keep only
opposite-parity rows. Not necessarily real or color-invariant homotopy; use symmetry separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MatrixLet
open Landau Detect
open scoped Topology ContDiff
namespace BV
variable {G : Gauge}

lemma walk (G : Gauge) (k:ℤ) : ∃ A:Mover G, Calib (MatrixLet.one A) k:= by
   classical
   obtain ⟨X,hX⟩:= tune G k; let Z:=Finset.Icc (0:ℤ) k; let W:= Finset.Icc (-2:ℤ) 1; let Y:= ↑Z × ↑W  -- subtype syntax?
   let V (l:Y) := yields (G:=G) l.1.val l.2.val; let T:=⨆ l, V l
   have ht h q (p:Grade G) (he:h≤k) (hp:p∈yields h q): p∈T := by
       by_cases h':p=0; rw [h']; exact zero_mem _
       obtain ⟨hx,hB⟩:= canbe hp h'; exact le_iSup V ((⟨h,Finset.mem_Icc.mpr ⟨hx,he⟩⟩,⟨q,hB⟩):Y) hp
   haveI : ∀ l, FiniteDimensional ℂ (V l) := fun _=> seed_finite ..
   haveI : FiniteDimensional ℂ T := .of_fg (fg_iSup _ fun l=> Module.Finite.iff_fg.mp (inferInstance : Module.Finite ℂ (V l)))
   let R (i:Lane4 G) := LinearMap.proj (φ:=fun _:Lane4 G=>ℂ) i ∘ₗ X ∘ₗ T.subtype
   choose U B hB using fun i=> point_recovery T (R i)
   let α(i:Lane4 G):= Landau.parity i.1
   let A : Mover G := {
      source l:= (U l).filter fun u=> α u≠α l
      mat := B
      row i j h:= by have H: α j≠α i:= (Finset.mem_filter.mp h).2; exact (by change α j=(true ^^ α i); cases h0:α i <;> cases he:α j <;> simp_all) }
   have H h q (f:Grade G) (hx:h≤k) (hf:f ∈ yields h q) : MatrixLet.one A f= X f:= by
       ext i
       have hv : X f i=∑ j∈ U i,B i j*f j:= hB i ⟨f,ht h q f hx hf⟩
       change (∑ j∈ Finset.filter (fun j=>α j≠ α i) (U i), B i j*f j)=X f i
       by_cases hp: α i= Local.parity q
       · have HT : X f i=0:= by
             by_contra he
             have ht:= par_seed (hX.price h q f hx hf) i he; rw [par_sub,par_one] at ht; change α i = (Local.parity q ^^ true) at ht; rw [hp] at ht; exact (by cases Local.parity q <;> decide : (Local.parity q= (Local.parity q ^^ true)) → False) ht
         rw [HT]; exact Finset.sum_eq_zero fun j h=> mul_eq_zero_of_right _ (Classical.byContradiction fun hj=> (Finset.mem_filter.mp h).2 ((par_seed hf _ hj).trans hp.symm))
       rw [hv]; refine Finset.sum_subset (Finset.filter_subset ..) fun j hj he=>?_ ; exact mul_eq_zero_of_right _ (Classical.byContradiction fun h'=> he (Finset.mem_filter.mpr ⟨hj,show α j≠α i from fun hint=>hp (hint ▸ par_seed hf _ h')⟩))
   have H' h q f (he:h≤k) (hf:f∈yields h q): joint (MatrixLet.one A) f = joint X f:= by rw [joint_at, H h q f he hf, H h (q+1) _ he (stays f h q hf)]; rfl
   refine ⟨A,⟨⟨fun h q f he hf=> (H h q f he hf).symm ▸ hX.price h q f he hf, fun h q f he hf=>?_⟩,fun h q f he hf=> ?_⟩⟩
   rw [H h (q+1) _ he (stays f h q hf), hX.double h q f he hf]
   rw [H' h q f he hf, H' h q _ he (hX.spectrum he hf), hX.lights h q f he hf]
end BV
end YM.MS.Local

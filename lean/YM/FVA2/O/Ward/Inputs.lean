import YM.FVA2.O.Ward.Transit
import YM.MS.Garment.Wick
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Differential
/-! anticommutator of Charge evaluated on the odd line.
Using the same cutoff χ as the MS theory. For static BV nilpotence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat
open MS.Local MS.Garment MS.Garment.Wick MS.Landau
-- dimensions generic
lemma partner {A:Type} [Fintype A][DecidableEq A] (f:Momentum A→ℝ) (i j: Landau.Atom A)(p:Momentum A): (stamp (id:Momentum A→Momentum A)).change (laplace f) i j p = 0 := by
   unfold Charge.change
   rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;>
       simp [ Fintype.sum_prod_type,Fintype.sum_option, stamp, Landau.p,cross, bare,laplace, Landau.delta , apply_ite Complex.ofReal, ite_mul, ite_div ];
   all_goals first| rw [ ← realK i j ]| skip
   all_goals ring
-- Supply actual at μ
variable {G:Gauge} (s:ℝ)
lemma noChange (m:ℕ): (Wick.Q G m).change (Wick.B0 G s m) = 0:= by
    unfold Q B0; rw [City.land_charge id (fun x=> rfl)]; ext i j q; unfold choir; simp_rw [partner]; simp
lemma zeroTrace (m:ℕ) (q) (F): (Q G m).raise (trc (B0 G s m) q F) = - trc (B0 G s m) q ((Q G m).raise F) := by
    have hm:= skew_change (F:=F) (Q G m) (cl_b G s m) q; rw [ noChange ] at hm; simp [trc] at *; linear_combination (norm:=abel) hm
lemma no_raise (f) : (Q G 0).raise ((Q G 0).raise f) = 0:= raise_nil _ fun a v p=> by
    simp_rw [← MatrixLet.charge]; exact congr_fun (Local.BV.Q_zero (G:=G) v) (a,p)
end YM.FVA2.O.Ward

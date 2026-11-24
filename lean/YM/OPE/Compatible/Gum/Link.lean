import YM.OPE.Compatible.Gum.Bacon
/-!
# Set moments to insertion Leibniz. constants common on two clusters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] {μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {p q:J→E→ℝ}[DecidableEq J] (t:Finset J)
local notation "W" => E → ℝ
section conv
variable {F: Finset J→ℝ} {a:J}[DecidableEq I]
lemma insertConv (i:J)(hi:i∉t)(h k:Finset J→ℝ): Con h k (insert i t)= Con (fun j=>h (insert i j)) k t+ Con h (fun j=> k (insert i j)) t:=by
      unfold Con; rw [powers_extend _ _ _ hi, add_comm]; apply congr_arg₂
      · apply sum_congr rfl; intro j hj; have he:insert i t \ insert i j=t \ j:=by ext x; have hp:i∉j:=fun x=>hi (mem_powerset.mp hj x); by_cases hx:x=i<;>simp [*]
        rw [he]
      apply sum_congr rfl; intro j hj; have he : insert i t \ j= insert i (t\j):=by ext x; have hp:i∉j:=fun x=>hi (mem_powerset.mp hj x); by_cases hx:x=i<;> simp [*]
      rw [he]
lemma powersAssoc (s:Finset J)(h k f:Finset J→ℝ): Con h (Con k f) s= Con (Con h k) f s:=by
       -- induct s, shift insert via Leib
       induction s using Finset.induction_on generalizing h k f with
       | empty => simp [Con,mul_assoc]
       | insert i s hi ih=>
           let S(q:Finset J→ℝ): Finset J→ℝ:=fun j=> q (insert i j)
           have hz : ∀ u⊆s,∀ (a b:Finset J→ℝ), S (Con a b) u = Con (S a) b u+Con a (S b) u:=by
             intro u hu a b; exact insertConv u i (fun x=> hi (hu x)) a b
           change S (Con h (Con k f)) s=S (Con (Con h k) f) s
           rw [hz s le_rfl,hz s le_rfl]; have ha : Con h (S (Con k f)) s=Con h (Con (S k) f) s+ Con h (Con k (S f)) s:=by unfold Con; rw [← sum_add_distrib]; exact sum_congr rfl fun j hj=>by rw [hz _ (sdiff_subset ..),mul_add]
           have hv: Con (S (Con h k)) f s=Con (Con (S h) k) f s+ Con (Con h (S k)) f s:=by unfold Con;rw [← sum_add_distrib]; exact sum_congr rfl fun j hj=>by rw [hz j (mem_powerset.mp hj),add_mul]
           rw [ha,hv,ih,ih,ih, add_assoc]
end conv
lemma loopIn (a:J)(p:J→E→ℝ)(ha:a ∉t)(f:W): Tap μ L p (f*p a) t= Tap μ L p f (insert a t)+Con (Tap μ L p f) (Tap μ L p (p a)) t:=by
      let X:=fun i:Finset J=> Tap μ L p f (insert a i); let V:=Tap μ L p f; let T:=Tap μ L p (p a); let A:= drink μ L p 1
      have hv (i:Finset J)(u: i⊆t):
         Con (fun k=>X k + Con V T k) A i= drink μ L p (f*p a) i:=by
          have hx:a ∉ i:= fun x=>ha (u x); have he :Con V A (insert a i)= drink μ L p (f*p a) i:= (stated ..).trans (by unfold drink powr; rw [prod_insert hx,mul_assoc]); have hh(j:Finset J)(h:j⊆i): A (insert a j) = Con T A j:=by
              rw [show Con T A j= _ from stated μ L p (p a) j]; unfold A drink powr; rw [prod_insert (fun (y:a∈j)=>hx (h y)),one_mul]
          rw [insertConv i a hx] at he; rw [← he]; unfold Con; simp_rw [add_mul,sum_add_distrib]; apply congr_arg; change Con (Con V T) A i=Con V (fun j=> A (insert a j)) i; rw [← powersAssoc]; exact Finset.sum_congr rfl fun j hj=>congr_arg (fun y:ℝ=>V j*y) (hh _ (sdiff_subset ..)).symm
      exact (agrees (fun i=> X i+Con V T i) A _ (sated μ L p) t hv).symm
end YM.OPE.Libra.Shell

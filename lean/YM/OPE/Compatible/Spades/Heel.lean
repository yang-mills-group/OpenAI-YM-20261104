import YM.OPE.Compatible.Spades.Scuff
/-!
# flop charge convergence
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{K:KernelChoices}
variable {I J:Type}[Fintype I]
section
noncomputable abbrev crewZ (p:Dual' (PAD I)):PAD I:= fun i=> p (Pi.single i 1)
lemma ArchC (p:Dual' (PAD I))(x:PAD I): crewZ p ⬝ᵥ x=p x:=by
     nth_rw 2 [show x=∑ i,x i • (Pi.single i 1: PAD I) from funext fun j=> by simp [Finset.sum_apply,Pi.single_apply]]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=>by rw [map_smul]; exact mul_comm ..
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (A:Law E)(L:E→L[ℝ] PAD I)
lemma Salvet (p q:Dual' (PAD I)): A.wick (p.comp L.toLinearMap) (q.comp L.toLinearMap)=crewZ p⬝ᵥ( chamber A L*ᵥcrewZ q):=by
     have hp (q:Dual' (PAD I)): q.comp L.toLinearMap=∑ i, crewZ q i • coQ L i:=by ext x; change q (L x)=_; rw [← ArchC q (L x),LinearMap.sum_apply]; rfl -- rw comp coercion
     rw [hp p,hp q]; unfold Law.wick; simp_rw [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]; unfold dotProduct ; apply Finset.sum_congr rfl;intro i _; unfold Matrix.mulVec dotProduct; rw [Finset.mul_sum]; apply Finset.sum_congr rfl;intro j _;congr 1; exact mul_comm .. 
end
noncomputable abbrev Cane (G:Gauge)(b:ℕ)(o:Site n):= floss G b o ∘L (flats G n).toContinuousLinearMap
variable (v:Train i)(hz:4 ≤ i)(K:KernelChoices)
lemma vibrate [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (L:Law E) (M:E→L[ℝ] Vec G n 1)(h: Licence M L v K)(b:ℕ):
     Chip (Vessel K v G n hz) (Cane G b o) (floss G b o ∘L M) L:=by
       constructor; let T:= (Vessel K v G n hz); let B:=floss G b o; let A:= (flats G n).toContinuousLinearMap; intro u w; let x(i:Dual' (Scoop G b)):= i.comp B.toLinearMap; have hp(g):Health (Prog K v G n) (crewZ (x g)):=by intro a he; rw[ArchC]; change g (B a)=0; rw [show B a=0 from flareK o K v hz a he b,map_zero]
       change T.wick ((x u).comp A.toLinearMap) ((x w).comp A.toLinearMap) = L.wick ((x u).comp M.toLinearMap) ((x w).comp M.toLinearMap); rw [Salvet,Salvet,show chamber T A=CapeV K G v n from (Hport K v G n hz).choose_spec.1,blankV _ hz _ (hp u)]; exact h _ _ (hp u) (hp w)
end YM.OPE.Spells

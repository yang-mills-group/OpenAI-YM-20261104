import YM.OPE.Compatible.Ice.Queue
import YM.OPE.Compatible.Chest.Wild
/-! # all-three-phase Φ limit.P remains local prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d e Z:ℕ}{n:Side}{ε v t s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea Quit.PriceZ Quit.Jac
variable {τ:Phase→ℕ}
section
variable (G)(K:KernelChoices) (hp:4 ≤ i)(τ:Phase→ℕ)(k:ℕ)
noncomputable abbrev Rise_φ (p:solar G k τ)(X:Train i)(u:Phase)(e:ℕ):Terra G τ k u:= Cap _ (upCap u e) _ _ (boostS (atlasF G X hp K) (1/2) (τ u) (k+u.val) (p.val u))
lemma Hear (H:Aware k τ)(hs:s<t)(he:e+6 ≤ Z+1)(ha:v ≤ 0)(ht:3*v ≤ s): ∃ F:ℝ→ℕ,∀ (l:Filter I)(c w:I→ℝ)(a:I→solar G k τ)(X:I→ Train i) (n:I→Side)(x:∀ i,Site (n i)), Tendsto c l atTop→(∀ᶠ i in l,F (c i) ≤ (n i).val) → Alive l c a → RateLE l c w v→ Audible G K n l c i Z X hp (fun i=> Aview (a i) (x i) (w i)) s → ∀ u:Phase, RateLE l c (fun i=> Rise_φ G K hp τ k (Ripple G H (w i) (a i)) (X i) u e) t:=by
       choose F hF using (fun u:Phase=>TriviaC G K hp k (I:=I) (τ:=τ) u hs (show upCap u e ≤ Z+1 from by unfold upCap;have hx:=u.isLt;omega)); let W(t:ℝ):= ∑ i,F i t; refine ⟨W,fun l c w a X n x hc hw hA hx hq u=> hF u l c (fun i=> Ripple G H (w i) (a i)) X n x hc ?_ (Franks hA H (hx.mono ha) hc) (crest_S n hp hc hA x H hq hx ha ht u) ⟩; filter_upwards [hw] with i hi; exact (single_le_sum (f:=fun u=> F u (c i)) (fun _ _=>Nat.zero_le _) (mem_univ _)).trans hi
end
end YM.OPE.Ibis

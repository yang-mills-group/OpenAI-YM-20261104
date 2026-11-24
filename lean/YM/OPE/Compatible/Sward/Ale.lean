import YM.OPE.Compatible.Sward.Army
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
variable (W:Aware d τ)(u:Phase)
local notation "S!"=>Seat (d+u.val) (τ u) (Shade H)
section
variable (p:Tracts H d τ)
abbrev Raft (A: RowB (Shade H))(t:Phase): empa H.ColorIndex (d+t.val) (τ t):=⟨boostS A (-(1/2:ℝ)) (τ t) (d+t.val) (p t).val,writ A (show (p t).val∈empa .. from ⟨fun i=> (merit (p t).property i).2.1,fun i=>(merit (p t).property i).1⟩) _⟩
noncomputable def FoldV (A:RowB (Shade H)):Tower (Shade H) d τ:=∑ i:Phase,scrollF H W i (Raft p A i)
lemma tideF (f:Filter I)(g:I→RowB (Shade H))(A:RowB (Shade H))(hp:Dull f g A): Tendsto (fun i=>FoldV W p (g i)) f (𝓝 (FoldV W p A)):=by
       unfold FoldV; apply tendsto_finsetSum _; intro i _; apply ContinuousAt.tendsto (scrollF H W i).continuous.continuousAt|>.comp; apply tendsto_subtype_rng.mpr; exact fixStrong (loreLap hp) (-(1/2)) _ tendsto_const_nhds
variable {P:Sponsor H}
lemma chartX (v: Train r)(h:4 ≤ r): FoldV W p (atlasF H v h P.K)=(Fallix H W P v h p).val:=by
      let q:= Larix H v h P.K W (-(1/2)) p; let R:= atlasF H v h P.K; rw [show (Fallix H W P v h p).val = ((solar H d τ).subtypeL) (Drift.relief H W q) from rfl,FoldV, Drift.relief, _root_.sum_apply,map_sum]; apply sum_congr rfl; intro i _; apply bloomP H d τ; change spread H d τ (scrollF H W i _) = spread H d τ (ascendF H W i (q i)); rw [splitF,pick H W i _, show (q i).val= _ from lavaX ..]
abbrev ratios (p:Tracts H d τ) (k:ℕ):Prop:= ∀ i:Phase, Deep (m:=τ i) (p i).val (k+3*(2-i.val))
open Flume.Script
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (Z:E→L[ℝ] Vec H N 1)[MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (A:Law E)
-- full card
lemma Mite (Y:I→E→Token)(p:Finset I)(h:∀ i∈p,MoldH A μ j (Y i)): MoldH A μ j (∑ i∈p,Y i):=by
      induction p using Finset.induction_on with
      | empty=> intro i;rw[sum_empty]; fin_cases i; all_goals exact trivialCost μ A
      | insert i p he ih=>rw [sum_insert he]; let v:=h i (mem_insert_self ..); let q:=ih (fun j hj=>h j (mem_insert_of_mem hj)); intro l; fin_cases l; exact (v 0).split (q 0); exact (v 1).split (q 1); exact (v 2).split (q 2)
-- full mark limit finite
lemma glossB (v:Train r)(h:4 ≤ r)(K:KernelChoices)(hA: Licence Z A v K)(hp:ratios p k):
        MoldH A μ k (fun i=> inkM (spread H d τ (FoldV W p (pointAt H v h K N))) d x ((flats H N).symm (Z i))):=by
         let U(j:Phase):= Aγ (N:=N) (m:=τ j) v h K (p j).val; let g(t:Phase):= radiusV x t Z (U t); have hx(j): (p j).val∈ empa ..:= ⟨fun i=>(merit (p j).property i).2.1,fun i=>(merit (p j).property i).1⟩; have hh:= Mite μ A g univ (j:=k) (fun j _=> cloakBaby x W j Z μ A v h K (p j).val hA (hx j) (hp j))
         convert hh using 1; funext i; let S:= spread H d τ; let t(j:Phase):=scrollF H W j (Raft p (pointAt H v h K N) j); rw[FoldV,map_sum, Finset.sum_apply]
         have he(j:Phase): Tide (S (t j)) d 0 ‖t j‖:=resin (t j) (fun _=> Nat.zero_le _); rw [inkify _ Finset.univ (fun j=>S (t j)) _ (fun j _=>he j)]; apply sum_congr rfl; intro j hj; rw [show S (t j)= _ from splitF _ _ _ _]
end
end
end YM.OPE.Silt.Phere

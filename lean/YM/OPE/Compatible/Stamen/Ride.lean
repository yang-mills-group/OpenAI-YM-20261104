import YM.OPE.Compatible.Stamen.Thor
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
variable {N:Side}{L:KernelChoices} (x:Site N)
local notation "F!"=>Vec H N 1
lemma chic (p:Seat k m (Shade H))(hp: settled (m:=m) p): formSong m k H x p∈harmon F! k:=by
       refine ⟨fun i hi=>?_,fun i v u=>?_⟩
       · ext1 u; rw[tensors,(sproutV m k _).1 i hi]; simp [scribe]
       rw [tensors,tensors, show deckW H N ∘ v ∘ u=(deckW H N ∘ v) ∘ u from rfl, ← rotating u, hp i u]
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (Z:E→L[ℝ] Vec H N 1)
noncomputable abbrev Charu (v:E):fieldX (Shade H):= upl x (deckW H N (Z v))
omit [FiniteDimensional ℝ E] in lemma Cuin (p:Seat k m (Shade H)) : (fun i=> Worth (m:=m) p (Charu x Z i))= Strike k (formSong m k H x p) ∘ Z:=by
       ext1 v; unfold Worth; unfold Function.comp Strike Tensor.diagonal; simp_rw[tensors]; rfl
omit [FiniteDimensional ℝ E] in lemma ChartU (p:Seat k m (Shade H)): anthem k (fun i=> Worth (m:=m) p (Charu x Z i)):=by rw[Cuin]; exact ((sailCost _ _).compLinear Z.toLinearMap)
-- color projections mores currency
lemma vim (a:Root (Shade H)): anthem k (fun i=> mores (Charu x Z i) k a):=by
     let q:=fun i:E=>Charu x Z i; let p:= coff (ships (moor a)) k; have hb: soot 0 p ((coffP H 1 k _ 0 (lumenD _)).choose*(↑(lawn (ships (moor a)))+1)^(0+2*k)):= (coffP H 1 k _ 0 (lumenD _)).choose_spec.2 _ (theater _)
     let U:= LinearMap.toContinuousLinearMap ((deckW H N).toLinearMap.comp Z.toLinearMap); let R:= orchestra p x; have hp(i):mores (q i) k a= Tensor.diagonal R (U i):=by
            unfold mores; rw [funext (moorEq _ a), coinShots]; exact (instruments p (sootS hb) x fun _=>U i).tsum_eq
     rw [funext hp]; exact ((lyricCost R).compLinear U.toLinearMap)
omit [FiniteDimensional ℝ E] in
lemma park (i:E): Quiet (Charu x Z i) 0:= by let z:= deckW H N (Z i); refine ⟨‖z‖,norm_nonneg _,fun u=>?_⟩; rw [show poise 0 _=(1:ℝ) from by unfold poise; ring,mul_one]; exact norm_le_pi_norm z _
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (A:PertExtension.GaussianScore.Law E)
variable (v:Train r)(h:4 ≤ r)(C:KernelChoices)
local notation "K!"=>Prog C v H N
open Matrix
abbrev Licence :Prop:= ∀ t w:F!, Health K! t→ Health K! w→ t ⬝ᵥ( PhV C v H N *ᵥw)=t ⬝ᵥ( chamber A Z *ᵥw) -- L binder order
abbrev Aγ (p:Seat k m (Shade H)):= boostS (pointAt H v h C N) (-(1/2)) m k p
lemma AuroraV (a:Seat k m (Shade H))(ht:0 < m)(hA: Licence Z A v C)(hp:a∈ empa H.ColorIndex k m)(he:Deep (m:=m) a j) :Husk μ A j (fun i=> Worth (m:=m) (Aγ (N:=N) (m:=m) v h C a) (Charu x Z i)):=by
       cases m with
       | zero=>omega
       | succ m=>
           let M:=Prog C v H N; let X:=M* PhV C v H N; rw[Cuin, show formSong (m+1) k H x (Aγ (m:=m+1) (N:=N) v h C a)= _ from finHeat ..]; apply Cloud.credit μ A Z (formSong (m+1) k H x a) X ?_ ?_ hA ?_ (chic x a hp.1) ?_
           · intro i y h; unfold X; rw[← Matrix.mulVec_mulVec, dotProduct_comm,invertG _ _ (alignZ _ _ _ ‹4 ≤ r›),h,dotProduct_zero] -- maybe alias
           · intro i hi; unfold X; rw [← Matrix.mulVec_mulVec]; exact HealthN h v i hi -- h arg
           · intro t; exact reserves _ v h t x (hp.2 t)
           intro i ht; ext1 t; rw[tensors, show lilies (m+1) k _ a i=0 from he i ht]; simp [scribe]
end
end YM.OPE.Silt.Phere

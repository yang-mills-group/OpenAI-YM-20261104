import YM.Integration.WilsonIndependentMatchedElectedFaces
import YM.Integration.WilsonIndependentMatchedRosterObserved
import YM.WilsonCoeffUV.Marked.Capture.AtSensor

/-! At any finite load the accepted ordinary income controls the large
period readings of the same normalized finite computation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedFiniteFees
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08
open Wilson Tree Precision AnalyticNext.QuarticMatch.Sheets Exterior Next.Free
open Gauge Source Labels XSpace PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.StableStrip
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR
open WilsonIndependentMatchedElectedFaces (Sheet)
open WilsonIndependentMatchedRosterPlanted (response)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}

def portfolio (P:Fin (n+1)→Sheet G):Sheet G:=
  ⟨∑i,(P i).grade,MassP G ℝ n (fun i=>(P i).field),fun side=>∏i,(P i).print side,
    manCo _ _ (fun i=>(P i).funded),fun side=>by
    rw [poly_agate n (fun i=>(P i).field) (fun i=>(P i).grade) (fun i=>(P i).funded)]
    exact Finset.prod_congr rfl (fun i _=>(P i).actual side)⟩

def read (A:Levels G)(Ñ:ChartRatio G)(N q top stop:ℕ)
    (P:Fin (n+1)→Sheet G)(side:Side)(j:ℕ)(x:Fin 0→YForest G):ℝ:=
  WilsonIndependentConditionalMarkedCover.tensor
    (WilsonIndependentMatchedOrdinaryHistory.scalar A Ñ N q top stop (fun l=>∏i,(P i).print l) side)
    j 0 (slideC side x)

theorem heard (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {N q top stop:ℕ}(active:stop≤top)(cap:top≤N)(P:Fin (n+1)→Sheet G)
    (legal:(∑i,(P i).grade)≤q+1)(j:ℕ)(x:Fin 0→YForest G):
    Tendsto (fun side=>read A Ñ N q top stop P side j x) atTop
      (𝓝 ((cruises A Ñ N (q+1) top stop (MassP G ℝ n (fun i=>(P i).field))).2 j 0 x)):=by
  let J:=portfolio P
  exact (WilsonIndependentMatchedOrdinaryHistory.covered A simple ratio active cap J.field
    (J.funded.tall legal) J.print J.actual j 0).point x

theorem paid (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {N q top stop e u:ℕ}(active:stop≤top)(cap:top≤N)(P V:Fin (n+1)→Sheet G)
    (lP:(∑i,(P i).grade)≤q+1)(lV:(∑i,(V i).grade)≤q+1){C:ℝ}
    (bill:response e u (cruises A Ñ N (q+1) top stop (MassP G ℝ n (fun i=>(P i).field))-
      cruises A Ñ N (q+1) top stop (MassP G ℝ n (fun i=>(V i).field))) C)
    (j:ℕ)(requested:j≤e)(x:Fin 0→YForest G)(ε:ℝ)(positive:0<ε):
    ∀ᶠ side in atTop,‖read A Ñ N q top stop P side j x-read A Ñ N q top stop V side j x‖≤C+ε:=by
  have lim:=((heard A simple ratio active cap P lP j x).sub (heard A simple ratio active cap V lV j x)).norm
  have wage:=bill.2 j requested x
  exact (lim.eventually (gt_mem_nhds (lt_of_le_of_lt wage (lt_add_of_pos_right _ positive)))).mono
    (fun side h=>h.le)

end YM.Integration.WilsonIndependentMatchedFiniteFees

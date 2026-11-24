import YM.WilsonCoeffUV.Stable.AllCuts

/-! Rooted income for the signed kernel left by the finite normalized stencil fit.
Both insertions start on the same actual independent schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedKernelResidual
open WilsonCoeffUV WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k u e:ℕ}{F:Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

/-- The second stencil is the very same input at the very same top. The only
analytic top wage is the submitted, unamplified tensor's actual rooted norm. -/
def diagonal (L:Torch H T p v E W K)(L':ChorusLine H T p e E W U)(same:L'.arch=L.L)
    (m s N:ℕ)(live:L.L.V.anchor≤m)(top:m+s≤N)(P:TowerS G D)(ok:On k P)
    (A:ℝ)(positive:0≤A)(bill:∀j r:ℕ,j≤e→Fruit 0 1 u (P.2 j r) A):
    CutsP H T p v E W K U where
  L:=L
  L':=L'
  he:=same
  m:=m
  i:=s
  b:=N
  N:=N
  M:=N
  ha:=live
  hc:=top
  hn:=le_rfl
  hm:=le_rfl
  pt:=P
  pt':=P
  sp:=ok
  sp':=ok
  fuel:=A
  hf:=positive
  toll j r hj:=YieldP.same (bill j r hj) (trail_pos ..).le

/-- One credit works for arbitrary independently tested inputs before the
report, including rank zero and the full fitted unit. The subtraction is the
tally at this cutoff and every intermediate kernel is its actual successor. -/
theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃ C:Credit, ∀ L:CutsP H T p v E W K U,
      L.springP L.i=L.pt-Shrine L.Ntop L.tileP ∧
      (∀ i<L.i, Spout L.ax L.tx L.N (L.m+i) h k (L.springP (i+1))=L.springP i) ∧
      ∀ j≤e,∀ i≤L.i,∀ r:ℕ,
        Fruit 0 1 u ((L.springP i).2 j r)
          (C.buy L.Age*Real.exp (-(L.vesselsC.draws.S.scale L.ceilC -
                     L.vesselsC.draws.S.scale (L.m+i))/4)*L.fuel) := by
  obtain ⟨C, price⟩:=CutsP.moisture H T p v E W K U
  refine ⟨C,fun L=>⟨L.carve1,fun _ hi=>L.carve2 hi,?_⟩⟩
  intro j hj i hi r
  exact (price L j hj i hi r).wax

end YM.Integration.WilsonIndependentMatchedKernelResidual
end

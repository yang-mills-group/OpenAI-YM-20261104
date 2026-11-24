import YM.Gaps1020.Local.Vacuum
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Vacuum
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Daisy.Charity.RG12
open YM.RG01.Survive
open YM.ConnectedActivityE6.Blaze.Thermal1020

open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
variable (G:Gauge)

-- Arbitrary other Decal (scheduling future comparison/extraction) can coexist
-- with this Taylor family. Does not entitle a separately chosen Couture to
-- Thermal powers; need to produce this receipt on that exact history. `same`
-- includes Final, UV, OPE and every-phase witness domains from fashions.

theorem simultaneous (hG:G.Simple) (penalty:ℝ)(hp:0<penalty)(order:Extraction.Order)(Δ:Decal G):
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)(L:EveryPhase.Almanac U)
      (N:Couture C hG ((Thermal1020.vacuum G).paired Δ)),
      C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=penalty ∧
      UVExtension.Oasis.Floral (hG:=hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full (order.refine f).per).Ordered C T ∧
      (∀ d k:ℕ,∀ᶠ n:ℕ in atTop,∀ (r:ℕ)(v:Fin r→ C.book.Token),(∀ i,(v i).1≤d) → ∃ g, UVExtension.Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed U L ∧ Facilities C (order.refine f) T ∧
      C=Cellar.yard (roseA N.uses) N.cellar ∧ Programme N.uses N.cellar ∧
      ∃ (Q:Prescription U.sector.derivatives)(_hq:Q.Coherent), AllShapes U Q:=by
  obtain ⟨C,f,T,U,L,hM,hC,hpen,hF,hs,hp,hP,hU,⟨N⟩,Q,hq,hQ,hW,hR⟩:=YM.RG12.fashions G ((Thermal1020.vacuum G).paired Δ) hG penalty hp order
  refine ⟨C,f,T,U,L,N,hM,hC,hpen,hF,hs,hp,hP,hU,N.belongs,?_ ,Q,hq,hQ⟩
  exact provides (fun i x hx j h=> (N.couture i x hx j h).1) _ _ (N.belongs ▸ hM)
end YM.GapsLocal.Vacuum

import YM.Integration.WilsonPositionOriginalDressedQCohortSource
import YM.Integration.WilsonCoherentMayerPriorSource

/-! The two dated arm bounds, in their actual Q coefficient currency.
Both the signed source order and the genuine numerical test are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQPointArms
open Filter Finset Function Lattice Wilson RG Precision Source Marker Push.GridApprox
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open FullQLocal FullQLocal.RenderedStep Comparison.RG02 WilsonLimitConstruction
open RG3.Script.Picnic IterationFour.Vacuum MergeProof MergeProof.Accent
open MS MS.Menus MS.Local.Physical Extra.Histories ActualOriginalQReaders
open private reader from YM.Integration.WilsonReportingPrescribedOldScale
open scoped Classical Topology BigOperators
variable {G:Gauge}{V:Type}[Fintype V]{B:Deck G}
  (R:Run G)(simple:G.Simple)(u:V→MS.Rake.Label B)(J:Request V)(Q:MS.Land.Prescription B)(μ:ℝ)

include simple in
theorem original (K:ℕ):∃C:ℝ,0<C ∧ ∃e:ℕ,∀ᶠm:ℕ in atTop,∀(N p:ℕ)(o:V→Site (R.family.side (m+1) p))
    (orders:V→ℕ), (∀v,orders v≤K) →
    let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
    let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
    ∀ (x:IndependentTests (ActualRunQlocalNativeTuple.orbit D))(v:V)(U:Config G (R.family.side (m+1) p)),
      ‖WilsonPositionOriginalDressedQCohortSource.letter R Q D u η orders (testInclusion _ x) v U‖≤
        C*(R.family.path.levels.clock.hatBeta m)^e:=by
  obtain ⟨C,hC,e,late⟩:=WilsonSeparatedOriginalSlabQArms.original R Q u K μ simple
  let base:=ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)
  let M:ℝ:=1+∑v:V,|readerPrice base v|
  have mp:0<M:=by dsimp [M];positivity
  refine ⟨M*C,mul_pos mp hC,e,?_⟩
  filter_upwards [late] with m slab
  intro N p o orders cap D η x v U
  have atRoot:=ActualOriginalQReaders.native_reader_bound D v x
  change ‖ActualRunQlocalNativeTuple.reader D v (testInclusion _ x v)‖≤
    readerPrice (ActualOriginalQPointSetup.pointDatum R J p (m+1) o) v at atRoot
  rw [reader R J p (m+1) o v] at atRoot
  have term:|readerPrice base v|≤∑j:V,|readerPrice base j|:=
    single_le_sum (fun j _=>abs_nonneg (readerPrice base j)) (mem_univ v)
  have read:‖ActualRunQlocalNativeTuple.reader D v (testInclusion _ x v)‖≤M:=
    atRoot.trans ((le_abs_self _).trans (by dsimp [M];linarith only [term]))
  have fee:=slab (le_refl m) (WilsonReportHarvestUpperRange.latest R.family.S (le_refl m))
    v (orders v) (cap v) (R.family.side (m+1) p) (ActualRunQlocalNativeTuple.root D v) U
  have shift:η=μ-R.family.S.scale (m+1):=by dsimp [η];ring
  rw [WilsonPositionOriginalDressedQCohortSource.letter,shift,norm_mul,mul_assoc]
  exact mul_le_mul read fee (norm_nonneg _) mp.le

end YM.Integration.WilsonPositionOriginalDressedQPointArms

import YangMills.WilsonProof.NativeSupport.JointOwnerSheets
import YangMills.WilsonProof.NativeSupport.JointStage
import YangMills.WilsonProof.NativeSupport.FundedProjection
import YM.FullVolume.Nectar.Oust

/-! Both old measured coefficient sheets on an actual retained visit are the original physical Memoires at that same flight. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
set_option quotPrecheck false
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q d t d' t':ℝ}{N n m:ℕ}{L:Lyrics R t t}
open UniformSpace
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 140000
variable (H:Chord R N m n t t){T:Team (stageP A.B.a (m+1) n)}
local notation "P"=> (stageP A.B.a (m+1) n)
local notation "Q"=> A.B.a.budget (m+1)
local notation "Ω"=> A.B.a.clock.hatBeta (m+1)
local notation "β"=> A.B.a.clock.hatBeta m
local notation "S"=> A.B.a.S.side (m+1) n
local notation "α'"=> A.B.a.S.side m n
local notation "Ls"=> D.L (A.B.a.clock.J (m+1))
local notation "Q!"=> R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "Ce"=> fire G Ls β
local notation "Δe"=> thaw G Ls β
local notation "db"=> ((A.B.a.budget m).supportExponent)
local notation "dc"=> (Q).supportExponent
local notation "B₀"=> A.B.a.budget m
local notation "S'" => A.B.a.clock.op m n
open Board MergeProof Marker JointLoad Heir Merge Mallow Luna Frets Empire Imago
variable {V I:Type}[Fintype I][Fintype V][DecidableEq V] {W Z:Type} [SeminormedAddCommGroup W][NormedSpace ℝ W]
variable {B: Marker.Census V}
variable (g:G.Simple)
namespace Orchard
variable (w : V → ℝ) (o : V → Site (A.B.a.S.side (m+1) n))
open Accent Frets Cryst Menu Many
local notation "o'"=>(S').ratio.parent ∘ o
open UVNext.CouplingReset
variable {b e:ℝ}{U: In A.B.a m n} (Y:Spring R N m n b e U) (x:Set.Icc b e) 
variable (tone : Y.W=H.tone) (order : Y.ordinal=H.order (Rain.listIn (U b)))
open YM.Integration.InletSusceptibility YM.Integration.InletSusceptibility.NativeSwitch
variable (F:I → Lotus.Leaf (Cryst.flown Y x).val) (rA : I→ℝ)

include tone order in
theorem held_memos {D : Type} [DecidableEq D] (C : Census D) (z : I → Poly C) :
    Frets.memoE H (Cryst.flown Y x) F z rA = Photo.spine F (houseS Y x) Chi.canonical rA C z ∧
    Frets.memoK H (Cryst.flown Y x) F z rA = Photo.chain (Y.result x.val) (Many.pupilK Y x F rA) C z := by
  refine ⟨rfl,?_⟩
  unfold Frets.memoK
  rw [(Cryst.regarded H Y x tone order).1, show Cryst.brands H (Cryst.flown Y x) F rA=Many.pupilK Y x F rA from
    funext fun t=>funext fun p=>Cryst.palette H Y x tone order F rA t p]

include tone order in
theorem old_held_probe (marks : I → Finset (Bond (A.B.a.S.side m n)))
    (test : I → Bond (A.B.a.S.side m n) → ℝ → ℝ) (i:I) (old : marks i=∅) :
    SelectedKernel.spine F (houseS Y x) Chi.canonical marks test rA (YM.Stock.census Unit) (singleProbe i) =
      Frets.memoE H (Cryst.flown Y x) F (singleProbe i) rA ∧
    Photo.chain (Y.result x.val) (Many.Measured.pupilK Y x F rA marks test) (YM.Stock.census Unit) (singleProbe i) =
      Frets.memoK H (Cryst.flown Y x) F (singleProbe i) rA := by
  have original := held_memos H Y x tone order F rA (YM.Stock.census Unit) (singleProbe i)
  exact ⟨(SelectedKernel.inherited_spine F (houseS Y x) Chi.canonical marks test rA i old).trans original.1.symm,
    (Many.Measured.inherited_chain Y x F rA marks test i old).trans original.2.symm⟩

end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil

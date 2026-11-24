import YangMills.WilsonProof.NativeSupport.JointHeldProbes
import YangMills.WilsonProof.NativeSupport.JointMeasuredModes
import YangMills.WilsonProof.NativeSupport.JointPhysicalHeap
import YangMills.WilsonProof.NativeSupport.JointBornIntake

/-! Both projected old-mode scores use the funded original probes of the same retained physical heap. -/
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
open YM.Integration.InletSusceptibility.Painted YM.Integration.InletSusceptibility.Packet
local notation "o'"=>(S').ratio.parent ∘ o
open UVNext.CouplingReset
variable {b e:ℝ}{U: In A.B.a m n} (Y:Spring R N m n b e U) (x:Set.Icc b e) 
variable (tone : Y.W=H.tone) (order : Y.ordinal=H.order (Rain.listIn (U b)))
open YM.Integration.InletSusceptibility YM.Integration.InletSusceptibility.NativeSwitch
local notation "C" => Stock.census (Ink V)
local notation "PM" => (Stock.census (Ink V)).Mode
variable (Q₁:I → Hat (Stock.census (Ink V)) (Cryst.flown Y x).val) (vC:Ink V → ℝ) (positive:∀ i,0 < vC i)
variable (born:Finset V) (rooted:∀ i,∃ a∈(Q₁ i).s.val,a∈active born)
variable (J:Ink V → Finset (Bond (A.B.a.S.side m n))) (test:Ink V → Bond (A.B.a.S.side m n) → ℝ → ℝ)
variable (before:∀ a,a.1∉born → J a=∅)
local notation "L₀" => (fun i:Mound Q₁=>(heap Q₁ i).M)
local notation "fees" => (fun i:Mound Q₁=>sumFee (heap Q₁ i) vC)
local notation "marks" => (fun i:Mound Q₁=>JointLeaves.bonds J (heap Q₁ i).s.val)
local notation "tests" => (fun i:Mound Q₁=>JointLeaves.probe J test (heap Q₁ i).s.val)
local notation "painted" => (fun i:Mound Q₁=>sing (heap Q₁ i) vC)
local notation "rawK" => Many.Measured.pupilK Y x L₀ fees marks tests
local notation "oneName" => (Stock.census Unit).fire ()
local notation "pilot" i => NativeSwitch.singleProbe (Sum.inl i : Mound Q₁)
variable {dk ex kr:ℝ}
include positive rooted before tone order in
theorem held_old_scores (h:SelectedKernel.Usable L₀ (houseS Y x) Chi.canonical (Y.result x.val) marks tests fees rawK dk ex kr) (p:PM) (ne:p.val.Nonempty) (old:¬gains born p.val) :
    (∀ X Z,(SelectedKernel.spine L₀ (houseS Y x) Chi.canonical marks tests fees C painted X Z).part p =
      ∑ i:I,(Frets.memoE H (Cryst.flown Y x) L₀ (pilot i) fees X Z).part oneName*(sing (Q₁ i) vC).part p) ∧
    (∀ X Z,(Photo.chain (Y.result x.val) rawK C painted X Z).part p =
      ∑ i:I,(Frets.memoK H (Cryst.flown Y x) L₀ (pilot i) fees X Z).part oneName*(sing (Q₁ i) vC).part p) := by
  have quiet:p ≠ (Stock.census (Ink V)).quiet := fun eq=>ne.ne_empty (congrArg Subtype.val eq)
  obtain ⟨away,short⟩:=old_or_gain born p.val old
  have empty (i:I) (eq:(Q₁ i).s=p) : marks (.inl i)=∅ := by
    change ((Q₁ i).s.val.biUnion J)=∅
    rw [eq]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a mem
    obtain ⟨u,hu,uJ⟩:=mem_biUnion.mp mem
    rw [before u (disjoint_left.mp away (mem_image_of_mem _ hu))] at uJ
    exact notMem_empty a uJ
  have orig:=SelectedKernel.all_old_modes Q₁ vC positive (houseS Y x) Chi.canonical (Y.result x.val) marks tests rawK h
    (active born) rooted p empty quiet short
  constructor
  · intro X Z
    rw [orig.1]
    apply sum_congr rfl
    intro i _
    rw [(held_memos H Y x tone order L₀ fees (Stock.census Unit) (pilot i)).1]
  · intro X Z
    rw [orig.2]
    apply sum_congr rfl
    intro i _
    by_cases eq:(Q₁ i).s=p
    · have obs:=(old_held_probe H Y x tone order L₀ fees marks tests (.inl i) (empty i eq)).2
      let zf (d₀:DecidableEq (Mound Q₁)):=@NativeSwitch.singleProbe (Mound Q₁) d₀ (Sum.inl i)
      have unique (d₁ d₂:DecidableEq (Mound Q₁)):zf d₁=zf d₂:=congrArg zf (Subsingleton.elim _ _)
      have left (d₁ d₀:DecidableEq (Mound Q₁)) :
          Photo.chain (Y.result x.val) rawK (Stock.census Unit) (zf d₁)=
          Photo.chain (Y.result x.val) rawK (Stock.census Unit) (zf d₀) :=
        congrArg (Photo.chain (Y.result x.val) rawK (Stock.census Unit)) (unique _ _)
      have right (d₀ d₂:DecidableEq (Mound Q₁)) :
          Frets.memoK H (Cryst.flown Y x) L₀ (zf d₀) fees=Frets.memoK H (Cryst.flown Y x) L₀ (zf d₂) fees :=
        congrArg (fun u=>Frets.memoK H (Cryst.flown Y x) L₀ u fees) (unique _ _)
      exact congrArg (fun f:Box (A.B.a.S.side m n) → Config G (A.B.a.S.side m n) → Marker.Poly (Stock.census Unit)=>
        (f X Z).part oneName*(sing (Q₁ i) vC).part p) ((left _ _).trans (obs.trans (right _ _)))
    · rw [Menu.sing,Poly.part_send,if_neg (Ne.symm eq),mul_zero,mul_zero]

end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil

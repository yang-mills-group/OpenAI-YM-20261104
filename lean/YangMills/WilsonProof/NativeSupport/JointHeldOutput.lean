import YangMills.WilsonProof.NativeSupport.JointHeldScores
import YangMills.WilsonProof.NativeSupport.JointProjectionLedger
import YangMills.WilsonProof.NativeSupport.JointPhysicalTariff

/-! Project the physical regular and forced sheets of one retained original
spring after the measured tagged step. Both original one-switch prices
are charged on this same heap. -/
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
open JointShadow
local notation "CC" => Stock.census (Ink V)
local notation "base" => Stock.census V
variable (Q₁:I → Hat (Stock.census (Ink V)) (Cryst.flown Y x).val)
variable (load:V → ℝ) (positive:∀ i,0 < load i) (site:V → Site (A.B.a.S.side (m+1) n))
variable (aOld aNew:ℝ) (aa:1 ≤ aOld) (dd:1 ≤ aNew) (born:Finset V)
variable (rooted:∀ i,∃ u∈(Q₁ i).s.val,u∈active born)
variable (J:Ink V → Finset (Bond (A.B.a.S.side m n))) (test:Ink V → Bond (A.B.a.S.side m n) → ℝ → ℝ)
variable (before:∀ i,i.1∉born → J i=∅)
local notation "wv" => weight load aOld aNew born
local notation "L₀" => (fun i:Mound Q₁=>(heap Q₁ i).M)
local notation "fees" => (fun i:Mound Q₁=>sumFee (heap Q₁ i) wv)
local notation "marks" => (fun i:Mound Q₁=>JointLeaves.bonds J (heap Q₁ i).s.val)
local notation "tests" => (fun i:Mound Q₁=>JointLeaves.probe J test (heap Q₁ i).s.val)
local notation "painted" => (fun i:Mound Q₁=>sing (heap Q₁ i) wv)
local notation "rawK" => Many.Measured.pupilK Y x L₀ fees marks tests
local notation "oneName" => (Stock.census Unit).fire ()
local notation "pilot" i => NativeSwitch.singleProbe (Sum.inl i : Mound Q₁)
local notation "coords" => ((S').ratio.parent ∘ site)
local notation "priceE" => fun (i:I) (_:sun) (X:Support (A.B.a.S.side m n)) (Z:Config G (A.B.a.S.side m n))=>
    (Frets.memoE H (Cryst.flown Y x) L₀ (pilot i) fees X Z).part oneName
local notation "priceK" => fun (i:I) (_:sun) (X:Box (A.B.a.S.side m n)) (Z:Config G (A.B.a.S.side m n))=>
    (Frets.memoK H (Cryst.flown Y x) L₀ (pilot i) fees X Z).part oneName
variable {M:ℕ} {histBudget incoming oldTotal:ℝ} (Θ:Tableau q 300)
include g tone order positive aa dd rooted before in
theorem held_output
    (fund:Ship.Fund H Θ histBudget incoming v d) (M0:0 < M)
    (occ:Extra.Multi.Occupancy (((A.B.a.clock.op m n).ratio.parent ∘ site) ∘ (Prod.fst : Ink V → V)) M)
    (pay:Offer (site ∘ Prod.fst) (heap Q₁) wv (A.B.a.budget (m+1)).B ((A.B.a.budget (m+1)).supportExponent-4) (incoming/M))
    (borel:∀ u,∀ b∈J u,Measurable (test u b))
    (unit:∀ u,∀ b∈J u,∀ z∈Set.Icc 0 (Push.BetaTransport.linkCap (A.B.a.clock.op m n)),‖test u b z‖ ≤ 1)
    (anchors:∀ u b,b∈J u → site u.1=(A.B.a.clock.op m n).ratio.embed b.1)
    (old_bill:∀ y:V,(∑ i:I with y∈(Q₁ i).s.val.image Prod.fst ∧ ¬gains born (Q₁ i).s.val,
      sumFee (Q₁ i) (fun u:Ink V=>load u.1)*MergeProof.load (Q₁ i).M) ≤ oldTotal)
    (probeE:∀ i:I,RollsUp (A.B.a.budget m) id (priceE i) (q/2) (A.B.a.budget m).supportExponent
       (tempo Θ (D.L (A.B.a.clock.J (m+1)))*(‖((sumFee (Q₁ i) wv:ℝ):ℂ)‖*MergeProof.load (Q₁ i).M)))
    (probeK:∀ i:I,RollsUp (A.B.a.budget m) Prod.fst (priceK i) (q/2) (A.B.a.budget m).supportExponent
       (Real.sqrt (A.B.a.clock.forcedAllowance m)*(‖((sumFee (Q₁ i) wv:ℝ):ℂ)‖*MergeProof.load (Q₁ i).M))) :
    ∃ (E':Support (A.B.a.S.side m n) → Config G (A.B.a.S.side m n) → Marker.Poly (Stock.census V))
      (K':Box (A.B.a.S.side m n) → Config G (A.B.a.S.side m n) → Marker.Poly (Stock.census V)),
      RGGapR2.Rough.Ledger coords E' K' (A.B.a.budget m).threshold ∧
      RootedSheet (A.B.a.budget m) id E' load (tempo Θ (D.L (A.B.a.clock.J (m+1)))*oldTotal+1/min aNew (aOld^2)) ∧
      RootedSheet (A.B.a.budget m) Prod.fst K' load (Real.sqrt (A.B.a.clock.forcedAllowance m)*oldTotal+2/min aNew (aOld^2)) ∧
      ∀ Z,Painted.project (SelectedKernel.given («S» := A.B.a.clock.op m n) L₀ marks tests fees CC painted Z)=
      play (Y.result x.val) base (exclaim (Y.result x.val).activities base+K') (fun U=>∑ i,E' i U) Z := by
  let Aout:=Y.result x.val
  have ring (i:Ink V):0 < wv i := by
    have u:=positive i.1
    have xo:=zero_lt_one.trans_le aa
    have xn:=zero_lt_one.trans_le dd
    unfold Painted.weight
    split <;> split <;> positivity
  have input: (Cryst.flown Y x).val.p=A.B.a.budget (m+1) := (Cryst.flown Y x).property.1.point
  have payIn:Offer (site ∘ Prod.fst) (heap Q₁) wv (Cryst.flown Y x).val.p.B ((Cryst.flown Y x).val.p.supportExponent-4) (incoming/M) := by rw [input];exact pay
  have bm i b (_:b∈marks i) := JointLeaves.measurable_probe J test (heap Q₁ i).s.val borel b
  have bn i b (_:b∈marks i) := JointLeaves.unit_probe J test (heap Q₁ i).s.val unit b
  have root i b (mem:b∈marks i) := anchored_heap Q₁ (S') J wv payIn anchors i b mem
  obtain ⟨dk,ex,hd,capE,capK,live⟩:=measured_visit («H» :=H) («g» :=g) («w» :=wv) («o» :=site ∘ Prod.fst)
    («Y» :=Y) («x» :=x) («Θ» :=Θ) («fund» :=fund) («hmul» :=M0) («hX» :=occ) («hw» :=ring) («F» :=heap Q₁) («hF» :=pay)
    («marks» :=marks) («test» :=tests) («borel» :=bm) («unit» :=bn) («scope» :=root)
  let F:=SelectedKernel.spine L₀ (houseS Y x) Chi.canonical marks tests fees CC painted
  let K:=Photo.chain Aout rawK CC painted
  have room i : GridApprox.Nil.Scoped {u|(coords ∘ Prod.fst) u∈(L₀ i).crest.image (S').ratio.parent} (painted i) :=
    GridApprox.Nil.scope_send _ _ _ fun u hu=>mem_image_of_mem _ (pay.sites i (mem_image_of_mem _ hu))
  have priced i:=Menu.paid (heap Q₁ i) ring
  have silent i:=(virtue (heap Q₁ i) wv).1
  have nil i:=(virtue (heap Q₁ i) wv).2
  have reg i := SelectedKernel.serenade L₀ (houseS Y x) Chi.canonical Aout marks tests fees rawK CC painted live
    (coords ∘ Prod.fst) room wv ring priced silent bm bn root i
  have gas i := SelectedKernel.heavily L₀ (houseS Y x) Chi.canonical Aout marks tests fees rawK CC painted live
    (coords ∘ Prod.fst) room wv ring priced i
  have entireE := (SelectedKernel.exquisite L₀ (houseS Y x) Chi.canonical Aout marks tests fees rawK CC painted live wv ring priced).shrink hd capE ring
  have entireK := (Photo.excavation Aout rawK CC painted wv ring priced live.gas Aout.p.exponent_pos.le).shrink le_rfl capK ring
  have vacuum i Z:=SelectedKernel.selfie L₀ (houseS Y x) Chi.canonical Aout marks tests fees rawK CC painted live wv ring priced silent Z i
  have eqs p ne old:=held_old_scores («H» :=H) («Y» :=Y) («x» :=x) («tone» :=tone) («order» :=order) («Q₁» :=Q₁)
    («vC» :=wv) («positive» :=ring) («born» :=born) («rooted» :=rooted) («J» :=J) («test» :=test) («before» :=before)
    («h» :=live) p ne old
  have tempo0 : 0 ≤ tempo Θ (Ls) := by unfold tempo; have hΘ:=Θ.sane; positivity
  let E' i Z:=Painted.project (F i Z)
  let K' i Z:=RGGapR2.Rough.purge base (Painted.project (K i Z))
  have realOut:=projected_ledger Aout coords F K reg gas vacuum
  refine ⟨E',K',realOut.1,?_,?_,fun Z=>?_⟩
  · exact projected_transfer (A.B.a.budget m) id F coords aa dd tempo0 load positive born
      (fun i=>(reg i).toBorne) entireE Q₁ priceE probeE (fun i Z p ne old=>(eqs p ne old).1 i Z) old_bill
  · apply rooted_purge
    exact projected_transfer (A.B.a.budget m) Prod.fst K coords aa dd (Real.sqrt_nonneg _) load positive born
      (fun i=>(gas i).toBorne) entireK Q₁ priceK probeK (fun i Z p ne old=>(eqs p ne old).2 i Z) old_bill
  · have expands:=SelectedKernel.expansion L₀ (houseS Y x) Chi.canonical Aout marks tests fees rawK CC painted nil live wv ring priced silent Z
    exact (congrArg Painted.project expands).trans (realOut.2 Z)

end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil

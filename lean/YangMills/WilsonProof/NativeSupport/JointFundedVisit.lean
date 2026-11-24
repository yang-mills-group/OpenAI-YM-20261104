import YangMills.WilsonProof.NativeSupport.JointStage
import YangMills.WilsonProof.NativeSupport.FundedProjection
import YM.FullVolume.Nectar.Oust

/-! Rooted numerical measured purchase on an original held physical visit. -/
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
variable (Θ : Tableau q 300) {M : ℕ} {a u₀ : ℝ} (hw : ∀ i, 0 < w i)
  (fund : Ship.Fund H Θ a u₀ v d) (hmul : 0 < M)
  (hX : Extra.Multi.Occupancy ((A.B.a.clock.op m n).ratio.parent ∘ o) M)
open YM.Integration.InletSusceptibility
include g fund hmul hw hX
theorem measured_visit (F : I → Menu.Hat B (Cryst.flown Y x).val)
    (hF : Offer o F w (Q).B (dc-4) (u₀/M))
    (marks : I → Finset (Bond α')) (test : I → Bond α' → ℝ → ℝ)
    (borel : ∀ i, ∀ j ∈ marks i, Measurable (test i j))
    (unit : ∀ i, ∀ j ∈ marks i, ∀ z ∈ Set.Icc 0 (Push.BetaTransport.linkCap (S')), ‖test i j z‖ ≤ 1)
    (scope : ∀ i, ∀ j ∈ marks i, (S').ratio.embed j.1 ∈ (F i).M.crest) :
    let ft i := (F i).M
    let fees i := sumFee (F i) w
    ∃ dk ex : ℝ, db ≤ dk ∧ ex ≤ 1 ∧ (straw (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) Ls G β) ≤ 2 ∧
      SelectedKernel.Usable ft (houseS Y x) Chi.canonical (Y.result x.val) marks test fees
        (Many.Measured.pupilK Y x ft fees marks test) dk ex (straw (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) Ls G β) := by
    intro ft U'
    let u := Cryst.flown Y x
    have hm := H.paid
    have h : Rooms H Θ M (a/M) v d := { fund.rooms with bill := palette_multiplicity fund.rooms.bill M hmul }
    have he := palette_multiplicity fund.issued M hmul
    have hre : u₀ ≤ a := (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le fund.positive.le)).trans fund.foldE
    have ha : 0 ≤ a/M := div_nonneg (fund.positive.le.trans hre) (Nat.cast_nonneg _)
    let Bp:=A.B.a.budget (m+1); have hf:u.val.p= Bp:=u.property.1.point
    let hA := h.hA; let y:= A.B.a.clock.hatBeta m; let hh:= step_paid A.B.a m; have hJ:= hA _ _ (A.B.valid.pays m) _ hh; let E:=(R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m))
    obtain ⟨A₀,b,y₁,fY,kp,Yxg₁,p',P',gP,v',z,hB,hU,N₀,hN'⟩:=hJ.1.2 _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full) _ _ (houseS Y x)
    let B':=(A.B.a.budget m)
    have hY : B'.supportExponent+3≤ E.earn:= by rw [show B'.supportExponent= (A.B.a.params m).supportExponent from rfl, params_eq A.B.valid m]; exact R.pledging.agenda _ _ hh|>.1
    have ht : Offer o F w u.val.p.B (u.val.p.supportExponent-4) (a/M) := by
      apply Offer.fatten _ (div_le_div_of_nonneg_right hre (Nat.cast_nonneg _))
      rw [hf]; exact hF
    have hT:Palette.Plot ft (houseS Y x) U':= Photo.bidding _ B w hw F o hJ.1.1 (by rw [(houseS Y x).laws.intake.sizes,(houseS Y x).laws.data.funds.length_eq]; exact hB.covers) (by change 4 ≤ (Q!).exp+_+_; linarith only [hY,h.support,E.worth,E.first,E.second,(Q!).usable,(Q!).pos]) (hf ▸ h.sB) ha ht hX he
    let hv := Many.Measured.usable g hm Y x ft U' marks test borel unit scope N₀ hA hB hT
    have hsμ : 0 ≤ R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) := (houseS Y x).laws.data.μ_pos.le
    have cap : (straw (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) Ls G β) ≤ 2 := by
      unfold straw lauge
      apply (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr ?_) zero_le_two).trans (by norm_num)
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by norm_num)) (sq_nonneg _)
    refine ⟨_, _, ?_, ?_, cap, hv⟩
    · linarith only [hY,hB.allow]
    obtain ⟨_,hs,_,_,hτ⟩ := Palette.field ft (houseS Y x) Chi.canonical U' hT hB N₀.balance
    have hz := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos ((Q!).mark Ls (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) β)).le) (show 0 ≤ (1-1/2:ℝ)⁻¹ by norm_num)) (budget_nonneg (hs 0))
    linarith only [hB.gains,hz,hτ]
end Orchard
end YM.PhysicalNext.Repeat.Muse.Veil

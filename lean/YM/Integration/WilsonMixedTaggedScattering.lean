import YM.Integration.WilsonMixedTaggedPhysicalJets
import YM.Integration.WilsonMixedTaggedPhysicalTest
import YM.Integration.WilsonMixedTaggedTestControl

/-! Arbitrary compact scattering tests on the original Wilson course. The same
purchased bouquet reconstructs the signed test at the physical residue
addresses of every date, and every product it uses has the full and stripped
programs on all lower dates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedTaggedScattering
open Filter Finset Function Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station OPE
open RG05Readout.Pulse RG05Readout.Nuclear
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {W:Type} [DecidableEq W] [Fintype W]

def order (s:W→ℕ):ℕ:=(∑v:W,(s v+2))+4*Fintype.card W

def Readout {b t N per:ℕ} (tN:t < N) (s:W→ℕ) (Ψ:Wave W) (J h:ℕ) (r η X price:ℝ)
    (P:(v:W)→Sight R.family (s v) per) (S:(v:W)→Emblems R.family (s v)) : Prop :=
  (∀bN:b ≤ N,∀v:(i:W)→Palette R.family (s i),∀m:ℕ,∀g:Body,
    Pulse.constellation s v r Ψ bN m g=Pulse.premiums R.family s m b r •
      ∑o∈Pulse.area (C:=R.family) (p:=per) (b:=b) J,Pulse.meet s v r Ψ bN o g) ∧
    ∀o∈Pulse.area (C:=R.family) (p:=per) (b:=b) J,∃F:E4→Wave W,
      Bouquet s Native.box (fun f=>Pulse.buy R.family b per o (r*η/2) f ∧
        WilsonMixedTaggedPhysicalTest.Purchased R tN.le o s P S h price f)
        F (Pulse.earn s R.family b (order s) η r*X) ∧
      WilsonMixedTaggedPhysicalJets.Exact s Ψ o r N F

theorem original {rail:Address.Rail R.family} {worth:Worth} {rates:ℕ→ℕ}
    (simple:G.Simple) (book:OPE.Package R.family worth rates rail)
    (stock:Storage R.family rail) (signed:UV.Lacquer R.family rail) (K d h p:ℕ) (large:5 ≤ K)
    {ε:ℝ} (ep:0 < ε)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda R.family.path.levels j))
    (s:W→ℕ) (grades:∀v,s v ≤ d) (Ψ:Wave W) (compact:IsCompact (tsupport Ψ.val))
    (apart:∀x∈tsupport Ψ.val,Function.Injective x) :
    ∃(B:ℕ→ℕ→ℝ) (S:∀e:ℕ,Push.RelayDifference.Cutoffs→Emblems R.family e) (k J:ℕ) (η X:ℝ),
      0 < η ∧ η ≤ 1 ∧ 0 < X ∧ Pulse.Scattering Ψ η ∧ Nuclear.Tall Ψ (order s+1) 1 X ∧
      ∀ᶠ r in 𝓝[>] (0:ℝ),let b:=crossLevel R.family.S r-1-1
        let t:=WilsonMeasuredWindow.stop R.family.path.levels simple K r
        b+1 < t ∧ Warm R.family b (d+1) k ∧ Fintype.card W*2 ≤ R.family.path.levels.clock.J b ∧
        ∀N:ℕ,∀tN:t < N,∀per:ℕ,∃P:(v:W)→Sight R.family (s v) per,
          (∀v,Spine rail B R.makes b per (s v) N (P v) (S (s v) (N,per))) ∧
          Readout R (b:=b) tN s Ψ J h r η X
            (ε*((Real.sqrt (R.family.path.rep N per t).beta)⁻¹)^p) P (fun v=>S (s v) (N,per)) := by
  have hk:0 < K:=by omega
  obtain ⟨η,e0,e1,far⟩:=WilsonMixedTaggedTestControl.separation Ψ compact apart
  obtain ⟨ρ,ρ0,span⟩:=WilsonMixedTaggedTestControl.range Ψ compact
  obtain ⟨X,x0,cap⟩:=WilsonMixedTaggedTestControl.derivatives Ψ compact (order s+1)
  let J:ℕ:=⌈ρ+2⌉₊
  obtain ⟨B,S,k,paid⟩:=WilsonMixedTaggedMovingCapture.original (W:=W) R simple book stock signed
    K d h p hk ep slow
  refine ⟨B,S,k,J,η,X,e0,e1,x0,far,cap,?_⟩
  filter_upwards [paid,WilsonMixedTaggedClearance.mesh R J,
    WilsonAllDateHarvestClearance.calendar R simple large e0,
    (WilsonMixedTaggedMeasuredWindow.original R simple K hk slow).2] with r funding scales room dates
  intro b t
  obtain ⟨_,_,filed⟩:=funding
  have bt:b+1 < t:=dates.1
  have le:b ≤ t:=by omega
  obtain ⟨rp,below,margin⟩:=scales
  refine ⟨bt,filed.1,filed.2.1,?_⟩
  intro N tN per
  obtain ⟨P,spine,catalogue⟩:=WilsonMixedTaggedPhysicalTest.cutoff filed s grades le tN rp e0 (margin per) room
  refine ⟨P,spine,?_,?_⟩
  · intro bN v m g
    apply Pulse.stanza bN s v r Ψ rp span
    have edge:ρ+2 ≤ (J:ℝ):=Nat.le_ceil _
    calc
      r*ρ+2*R.family.S.a b ≤ R.family.S.a b*ρ+2*R.family.S.a b :=
        add_le_add (mul_le_mul_of_nonneg_right below ρ0) (le_refl _)
      _ = R.family.S.a b*(ρ+2):=by ring
      _ ≤ R.family.S.a b*(J:ℝ):=mul_le_mul_of_nonneg_left edge (R.family.S.a_pos _).le
  · intro o near
    obtain ⟨F,terms,exactly⟩:=WilsonMixedTaggedPhysicalJets.original (N:=N) s o r η Ψ rp below e0 e1
      (show (∑v:W,(s v+2))+4*Fintype.card W < order s+1 from Nat.lt_succ_self _) far x0.le cap
    refine ⟨F,WilsonMixedTaggedPhysicalTest.relabel ?_ terms,exactly⟩
    exact fun f units funded=>⟨funded,catalogue o near f units funded⟩

end YM.Integration.WilsonMixedTaggedScattering

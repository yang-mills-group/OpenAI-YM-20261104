import YM.Integration.WilsonMixedTaggedMovingCapture
import YM.Integration.WilsonMixedTaggedClearance

/-! The physical test pays for each of its original normalized product terms.
At a fixed cutoff a single catalogue works for every root assignment and
every physical product term, with the true transported hard partners. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedPhysicalTest
open Filter Finset Function Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station OPE
open scoped Topology BigOperators Classical
open RG05Readout.Pulse RG05Readout.Nuclear
variable {W:Type} [Fintype W] [DecidableEq W] {G:Gauge} {R:Run G}

def Purchased (R:Run G) {b t N per:ℕ} (tN:t ≤ N) (o:W→Site (R.family.side b per))
    (s:W→ℕ) (P:(v:W)→Sight R.family (s v) per) (scale:(v:W)→Emblems R.family (s v)) (h:ℕ) (price:ℝ)
    (F:W→Body) : Prop :=
  ∀x:(v:W)→Palette R.family (s v),∀roster:Census W,∀{Q:ℝ},0 < Q →
    (∀v,size (x v) ≤ Q) →
    Q ≤ (R.family.path.levels.clock.hatBeta t)^h →
    WilsonMixedTaggedCapture.Delivered R b tN o (fun _=>(1,false)) s
      (fun z:ManyStem R.family o b=>F z.val.1) P scale x roster price

theorem cutoff {rail:Address.Rail R.family} {B:ℕ→ℕ→ℝ} {S:∀e:ℕ,Push.RelayDifference.Cutoffs→Emblems R.family e} {k d h p b t N:ℕ} {ε:ℝ}
    (filed:WilsonMixedTaggedMovingCapture.Filed (W:=W) R rail B S k d h p b b t ε)
    {J per:ℕ} (s:W→ℕ) (grades:∀v,s v ≤ d) (bt:b ≤ t) (tN:t < N)
    {r η:ℝ} (rp:0 < r) (ep:0 < η)
    (margin:2*(R.family.S.a b*(2*(J:ℝ)+1)) < R.family.S.radius per)
    (room:R.family.S.a t*(((R.family.path.levels.budget t).B^2+1:ℕ):ℝ) ≤ r*η/16) :
    ∃P:(v:W)→Sight R.family (s v) per,
      (∀v,Spine rail B R.makes b per (s v) N (P v) (S (s v) (N,per))) ∧
      ∀o∈Pulse.area (C:=R.family) (b:=b) (p:=per) J,∀F:W→Body,
        (∀v,Nuclear.Tall (F v) (s v+2) 1 1) →
        Pulse.buy R.family b per o (r*η/2) F →
        Purchased R tN.le o s P (fun v=>S (s v) (N,per)) h
          (ε*((Real.sqrt (R.family.path.rep N per t).beta)⁻¹)^p) F := by
  obtain ⟨P,spine,course⟩:=filed.2.2 N tN per s grades
  refine ⟨P,spine,?_⟩
  intro o near F units bought x roster Q qp charges bound
  apply course o (fun _=>(1,false)) (fun z=>F z.val.1) x roster
  · intro z j hj y _
    simpa only [one_pow,one_mul] using units z.val.1 j hj y
  · exact qp
  · exact charges
  · exact bound
  · exact WilsonMixedTaggedClearance.atDate o s F bt near margin rp ep bought room roster

omit [DecidableEq W] in
theorem relabel {E:Type} [TopologicalSpace E] {Ω:Set E} {s:W→ℕ} {A Z:Nuclear.Allow W}
    {X:E→Wave W} {price:ℝ} (pay:∀F,(∀v,Tall (F v) (s v+2) 1 1) → A F → Z F)
    (h:Bouquet s Ω A X price) : Bouquet s Ω Z X price := by
  induction h with
  | empty=>exact .empty
  | bloom F c a hc cap pos units paid=>exact .bloom F c a hc cap pos units (pay F units paid)
  | add _ _ left right=>exact left.add right
  | permit _ eq bill rec=>exact rec.permit eq bill

end YM.Integration.WilsonMixedTaggedPhysicalTest

import YM.Integration.WilsonMixedTaggedUniformCapture
import YM.Integration.WilsonMixedTaggedCatalogue

/-! The original funded catalogue supports every base between its fixed
threshold and the physical crossing predecessor, with one common depth
for all of them. It in particular supports the moving compact bases. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedTaggedMovingCapture
open Filter Finset Function Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station OPE
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {W:Type} [DecidableEq W] [Fintype W]
variable {D:Address.Rail R.family} {worth:Worth} {rates:ℕ → ℕ}

def Filed (D:Address.Rail R.family) (B:ℕ → ℕ → ℝ)
    (S:∀e:ℕ,Push.RelayDifference.Cutoffs → Emblems R.family e) (k d h p n b t:ℕ) (ε:ℝ) : Prop :=
  Warm R.family n (d+1) k ∧ Fintype.card W*2 ≤ R.family.path.levels.clock.J n ∧
    ∀N:ℕ,∀tN:t < N,∀per:ℕ,∀s:W → ℕ,(∀v,s v ≤ d) →
          ∃P:(v:W) → Sight R.family (s v) per,
            (∀v,Spine D B R.makes n per (s v) N (P v) (S (s v) (N,per))) ∧
            ∀(o:W → Site (R.family.side n per))(E:W → Motion)(q:ManyStem R.family o n → Body)
              (x:(v:W) → Palette R.family (s v))(roster:Census W){Q:ℝ},
              (∀v:ManyStem R.family o n,Cap (s v.val.1+2) (q v) 1) → 0 < Q →
              (∀v,size (x v) ≤ Q) → Q ≤ (R.family.path.levels.clock.hatBeta t)^h →
              Clearance o E s (headings o E q) roster t →
              WilsonMixedTaggedCapture.Delivered R b tN.le o E s q P (fun v=>S (s v) (N,per))
                x roster (ε*((Real.sqrt (R.family.path.rep N per t).beta)⁻¹)^p)

theorem uniform (simple:G.Simple) (book:OPE.Package R.family worth rates D)
    (stock:Storage R.family D) (signed:UV.Lacquer R.family D) (K d h p:ℕ) (hk:0 < K)
    {ε:ℝ} (ep:0 < ε)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda R.family.path.levels j)) :
    ∃ (B:ℕ → ℕ → ℝ) (S:∀e:ℕ,Push.RelayDifference.Cutoffs → Emblems R.family e) (k floor:ℕ),
      ∀ᶠ r in 𝓝[>] (0:ℝ),let b:=crossLevel R.family.S r-1-1
        let t:=WilsonMeasuredWindow.stop R.family.path.levels simple K r
        let extent:=(R.family.path.levels.budget t).B
        floor ≤ b ∧ ∃D₀:ℕ,D₀*(4*extent+2)+2*extent ≤ extent^2 ∧
          ∀n:ℕ,floor ≤ n → n ≤ b → Filed (W:=W) R D B S k d h p n b t ε := by
  obtain ⟨B,S,k,paid⟩:=WilsonMixedTaggedCatalogue.original R simple book stock signed W d
  obtain ⟨floor,all⟩:=Filter.eventually_atTop.1 paid
  refine ⟨B,S,k,floor,?_⟩
  have window:=(WilsonMixedTaggedMeasuredWindow.original R simple K hk slow).2
  filter_upwards [WilsonMixedTaggedUniformCapture.original (W:=W) R simple K d k h p hk ep slow,
    (WilsonMixedTaggedSpend.lower R).eventually_ge_atTop floor,window] with r report large scope
  intro b t extent
  obtain ⟨D₀,room,course⟩:=report
  refine ⟨large,D₀,room,?_⟩
  intro n grown nb
  have entry:=all n grown
  refine ⟨entry.1,entry.2.1,?_⟩
  intro N tN per s degrees
  have bt:b+1 < t:=scope.1
  obtain ⟨P,basis⟩:=entry.2.2 N (by omega) per s degrees
  refine ⟨P,basis,?_⟩
  intro o E q x roster Q caps qp charge qh clear
  exact course n nb N tN per o E s q book stock P (fun v=>S (s v) (N,per)) x roster
    entry.1 entry.2.1 basis degrees caps qp charge qh clear

theorem original (simple:G.Simple) (book:OPE.Package R.family worth rates D)
    (stock:Storage R.family D) (signed:UV.Lacquer R.family D) (K d h p:ℕ) (hk:0 < K)
    {ε:ℝ} (ep:0 < ε)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG05Readout.Lambda R.family.path.levels j)) :
    ∃ (B:ℕ → ℕ → ℝ) (S:∀e:ℕ,Push.RelayDifference.Cutoffs → Emblems R.family e) (k:ℕ),
      ∀ᶠ r in 𝓝[>] (0:ℝ),let b:=crossLevel R.family.S r-1-1
        let t:=WilsonMeasuredWindow.stop R.family.path.levels simple K r
        let extent:=(R.family.path.levels.budget t).B
        ∃D₀:ℕ,D₀*(4*extent+2)+2*extent ≤ extent^2 ∧ Filed (W:=W) R D B S k d h p b b t ε := by
  obtain ⟨B,S,k,floor,paid⟩:=uniform (W:=W) R simple book stock signed K d h p hk ep slow
  refine ⟨B,S,k,?_⟩
  filter_upwards [paid] with r report
  intro b t extent
  obtain ⟨grown,D₀,room,spend⟩:=report
  exact ⟨D₀,room,spend b grown le_rfl⟩

end YM.Integration.WilsonMixedTaggedMovingCapture

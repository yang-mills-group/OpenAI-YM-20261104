import YM.FullVolume.Cross
import YM.Integration.WilsonMixedTaggedFields
import YM.RG05Readout.Harvest.Spec
import YM.RG05Readout.Chalice.Choir

/-! The original financed Wilson catalogue supplies one sufficiently large
base date for the doubled finite roster, before any physical radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedCatalogue
open Function Filter Set Finset Lattice Wilson RG OPE RG05Readout RG05Readout.Many
open RG05Readout.Address RG05Readout.Records PhysicalNext.Repeat.Legato Bid
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {D:Address.Rail R.family} {worth:Worth} {rates:ℕ → ℕ}

theorem original (simple:G.Simple) (book:OPE.Package R.family worth rates D)
    (stock:Storage R.family D) (signed:UV.Lacquer R.family D) (V:Type) [Fintype V] (d:ℕ) :
    ∃ (B:ℕ → ℕ → ℝ) (S:∀e:ℕ,Push.RelayDifference.Cutoffs → Emblems R.family e) (k:ℕ),
      ∀ᶠ n:ℕ in atTop,Warm R.family n (d+1) k ∧ Fintype.card V*2 ≤ R.family.path.levels.clock.J n ∧
      ∀N:ℕ,n ≤ N → ∀per:ℕ,∀s:V → ℕ,(∀v,s v ≤ d) →
        ∃P:(v:V) → Sight R.family (s v) per,
          ∀v,Spine D B R.makes n per (s v) N (P v) (S (s v) (N,per)) := by
  obtain ⟨B,accounts⟩:=Harvest.elder book stock simple signed
  choose threshold funded using fun e:ℕ=>((accounts 0 0 0 e).1.mono (fun _ h=>h.2.2)).exists
  obtain ⟨S,rows⟩:=Chalice.opening R.makes threshold funded
  obtain ⟨k,dates⟩:=(accounts 0 0 d 0).2
  let start:=∑e∈Finset.range (d+1),threshold e
  refine ⟨B,S,k,?_⟩
  filter_upwards [dates,eventually_ge_atTop start,R.family.path.levels.fits.deep.eventually_ge_atTop
    (Fintype.card V*2)] with n warm old fit
  refine ⟨warm,fit,?_⟩
  intro N nN per s deg
  have head (v:V):threshold (s v) ≤ n:=by
    apply le_trans _ old
    exact Finset.single_le_sum (fun e _=>Nat.zero_le (threshold e))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (deg v)))
  let entry(v:V):=rows.paid (N,per) (s v) ((head v).trans nN)
  exact ⟨fun v=>(entry v).choose,fun v=>Records.Spine.tail R.makes _ _ (entry v).choose_spec (head v)⟩

end YM.Integration.WilsonMixedTaggedCatalogue

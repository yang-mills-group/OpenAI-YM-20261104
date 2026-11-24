import YM.Integration.WilsonConditionalTaylorFields
import YM.Integration.WilsonConditionalTaylorLabels
import YM.Integration.WilsonConditionalTaylorPosterior
import YM.Integration.FVA1Physical.Wilson.FluctuationMasks

/-! The true ordinary Wilson stencil has a finite-order uncut conditional
estimate on one funded existence witness for all original labels, masks and
translations, including the empty insertion and arbitrary repeated labels. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorPhysical

open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection Next.Foundations
open MSbar MSbar.Heath FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open WilsonConditionalTaylorLabels WilsonConditionalTaylorThreshold WilsonConditionalTaylorCalendar
open WilsonConditionalTaylorFieldPurchase WilsonConditionalTaylorFields WilsonWindowJointPurchase
open RGComparison.Core16.Spool
open scoped Classical Topology BigOperators

universe u
variable {G : Gauge}

def roster (G : Gauge) (n : ℕ) : ↥(entry G n).2 → Lamp G := packet (entry G n)

def fare (V : Voice G) (clear : Clear G V) (simple : G.Simple) : ℕ → MapPrices → Fare :=
  fun n _ => fluctuationMenu (roster G n) V clear simple

/-- Heights, cutoffs, torus, anchor and boundary remain common to both complex
components and every occupied subset of each finite requested roster. The
receiver reads the original true interacting measure and the independent field bank. -/
theorem masks (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G) (cle : Clear G V)
    (inventory : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
    (issued : Due (roster G) u V R.kit) (fund : Paid (atlas (fare V cle simple)) R.kit)
    (a : Roster G) : FluctuationMaskReadings (lamps a) R u := by
  obtain ⟨frame,_,vac⟩ := inventory
  have eachCode (n : ℕ) : FluctuationReadings (roster G n) R u :=
    WilsonConditionalTaylorFields.physical _ simple R u V cle frame
      (WilsonConditionalTaylorCalendar.read R (fare V cle simple) fund n)
      (WilsonConditionalTaylorFields.ports (roster G) n simple R u V issued vac) vac
  have eachEntry (e : Entry G) : FluctuationReadings (packet e) R u := by
    let statement : Entry G → Prop := fun v=>FluctuationReadings (packet v) R u
    exact (congrArg statement (recover_entry e)).mp (eachCode (Encodable.encode e))
  intro p s L hs D η hD hη
  let terms := (univ : Finset (Finset (Fin a.length)))
  have each (t : Finset (Fin a.length)) := eachEntry ⟨a,t⟩ p s L hs D η hD hη
  filter_upwards [terms.eventually_all.mpr (fun t _ => each t)] with k paid N n kn
  have empty := paid ∅ (mem_univ _) N n kn
  refine ⟨empty.1,?_⟩
  intro S scene j kj jN
  refine ⟨(empty.2 S scene j kj jN).1,?_⟩
  intro b Z hZ t part
  exact ((paid t (mem_univ _) N n kn).2 S scene j kj jN).2 b Z hZ part

/-- Single physical choice, before every finite list of original field labels
and translations. The true posterior and the continuum proof belong to this
very same `R`; additional prepaid physical outputs are preserved. -/
theorem select (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (u : G.ColorIndex) (V : Voice G) (cle : Clear G V)
    (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      more R.kit ∧ WilsonConditionalTaylorPosterior.Posterior R u ∧
      (∀ a : Roster G, FluctuationMaskReadings (lamps a) R u) ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      PhysicalNext.Repeat.Legato.Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors := by
  obtain ⟨R,T,W,⟨outside,issued,fund⟩,inventory,posterior,corr,original,citizen,logBook⟩ :=
    WilsonConditionalTaylorPosterior.select.{u} simple hε u V cle (Together (@more) (Together
      (@Due G _ _ (roster G) u V) (@Paid G (atlas (fare V cle simple)))))
      (fun s M => joint (credit s M) (joint (WilsonConditionalTaylorFieldPurchase.prepaid (roster G) simple u V cle s _)
        (WilsonConditionalTaylorThreshold.prepaid (atlas (fare V cle simple)) s _)))
  exact ⟨R,T,W,outside,posterior,masks R simple u V cle inventory issued fund,corr,original,citizen,logBook⟩

end YM.Integration.WilsonConditionalTaylorPhysical
end


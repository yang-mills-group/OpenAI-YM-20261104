import YM.Integration.FVA1Physical.Wilson.ResetJets
import YM.Comparison.RG02.Symphony.Grown

/-! The independent momentum-space coupling detector and the measured reset agree
to the purchased kinetic accuracy on the very same physical Run. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato
open Comparison.RG02 Comparison.RG02.Symphony Push.Loops
open scoped Classical

variable {G : Gauge} (A : Run G) {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {N m r : ℕ} (hm : m < N) (hs : G.Simple)
    (F : ∀ p, Forest (A.family.path.levels.clock.op m p).ratio)
    (t : ∀ p, (A.family.path.levels.clock.op m p).Choices)
    (W : ∀ p, Bulk.Colors R G (A.family.side (m+1) p)) (hW : ∀ p, (W p).Standard)

include hs hW

/-- The independently computed Fourier/Wilson coupling detector on all tori selects
the very kinetic reset used above. Inherited colors may vary with period; the kinetic
response, cutoff and all volume receipts come from the one selected Run. -/
theorem predicted_is_canonical_two (hr : 2 ≤ r) :
    let L := RunFormalChain.fromRun A
    Grown.Canon (quadraticCaliber (L.kin.alpha N m)) (Roster.series L N m r hm F t W) 2 := by
  intro L
  constructor
  intro k hk
  refine ⟨Roster.core L N m k,
    Roster.supply L N m r hm k A.alloy.B.plan
      (fun _ => A.kit.pledging.conducts.full N m _ hm.le) F t W hr hW hs hk, ?_⟩
  intro a
  interval_cases k
  · simpa [Roster.core,quadraticCaliber] using Roster.pays L N m hm A.alloy.B.plan a
  · simp [Roster.core,quadraticCaliber,zero_probe]
  · simpa [Roster.core,quadraticCaliber] using Roster.keeps L N m hm A.alloy.B.plan a

/-- Any all-order scheme satisfying the independent canonical detector on this same
bank must have this second coefficient. Its error against the actual inverse-coupling
step is bounded on every period by the purchased reset. -/
theorem canonical_ratio_price (hr : 2 ≤ r) (a : G.ColorIndex) (C : Adjacent.Caliber)
    (hC : Grown.Canon C (Roster.series (RunFormalChain.fromRun A) N m r hm F t W) r) :
    C.measure 2 = (RunFormalChain.fromRun A).kin.alpha N m ∧
      ∀ p, |C.measure 2 - measuredReset A N m p| ≤ resetPrice A m := by
  let L := RunFormalChain.fromRun A
  let S := Roster.series L N m r hm F t W
  let α := L.kin.alpha N m
  have h := Grown.unique_coeff S 2 2 (quadraticCaliber α) a (climbs A.family.path m)
    (predicted_is_canonical_two A hm hs F t W hW hr) (by omega) (d:=C) ⟨fun k hk => hC.paid k (hk.trans hr)⟩
  have eq : C.measure 2 = α := by simpa [quadraticCaliber] using h
  exact ⟨eq,fun p => eq ▸ measured_reset_price A hs hm⟩

end YM.Integration.FVA1Physical.Wilson

import YM.RG01Estimate.CensusStep
import YM.Integration.WilsonLimitConstruction.FundedSpringVacuum

/-! A single order-independent original cash guide on the actual funded
trajectory carries all finite cluster tails and the exact reassembled
coarse density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCensusVacuum

open Filter Lattice Wilson RG RG.Shoot AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep ConnectedActivityE6.Coat Push.SectorMeasure
open scoped Topology

variable {G : Gauge}

structure Station (R : Run G) (N p m : ℕ) where
  guide : Opera.Guide R.alloy.B R.kit.shape N m p (R.family.path.rep N p (m+1))
  price : Opera.Price R.alloy.B R.kit.shape N m p (R.family.path.rep N p (m+1)) guide
  band : (R.family.path.rep N p (m+1)).beta ∈ Shoot.band R.alloy.B.a (m+1)

def station (R : Run G) (N p m : ℕ) (hm : m < N) : Station R N p m :=
  Classical.choice (show Nonempty (Station R N p m) from by
    have h := (R.T.sticks N p).prices (m+1) (Nat.zero_le _) hm
    obtain ⟨H,he⟩ := Opera.feature R.alloy.B R.kit.shape hm
      R.kit.pledging.conducts.full R.kit.pledging.conducts.income h.1 h.2
    exact ⟨⟨H,he,h.2⟩⟩)

def Station.identity {R : Run G} {N p m : ℕ} (S : Station R N p m) :
    Match.Alliance S.guide S.guide 1 0 :=
  Match.staple (H:=S.guide) (J:=S.guide) rfl rfl rfl

/-- The station and its identity address map are chosen before the order. -/
theorem paid (R : Run G) (hG : G.Simple) (r : ℕ) : ∀ᶠ m : ℕ in atTop,
    ∀ (N p : ℕ) (hm : m < N), let S := station R N p m hm
      Account R.kit S.guide S.guide S.identity r := by
  filter_upwards [cluster_tail hG R.kit r] with m h N p hm S
  exact h N p hm _ _ S.guide S.guide S.identity S.price S.band

/-- The discarded signed source has its actual strong regular and forced
invoices, and the same coarse density factors with its additive remainder. -/
theorem resolution (R : Run G) (hG : G.Simple) (r : ℕ) : ∀ᶠ m : ℕ in atTop,
    ∀ (N p : ℕ) (hm : m < N), let S := station R N p m hm
      let L := R.alloy.B.a
      let U := R.family.path.rep N p (m+1)
      let V := R.family.path.rep N p m
      let X := ledger R.kit S.guide
      let D := discarded R.kit S.guide S.guide S.identity r
      let K := kept R.kit S.guide S.guide S.identity r
      let α := R.alloy.B.kin.alpha N m
      let q := (2*gStep U.beta)^(r+1)
      Collection.Local X (L.budget m) D q (Real.sqrt (L.clock.forcedAllowance m)*q) ∧
      ∀ (O : Tree.Forest (L.clock.op m p).ratio) z,
        V.eval z = earlyValue X V.path V.clip (L.budget m) K U.beta
            (Song.weighty S.guide Chi.canonical O) α z *
          Real.exp (-((X.read D).additive (L.budget m) z)) := by
  filter_upwards [paid R hG r] with m h N p hm S L U V X D K α q
  have hs := h N p hm
  refine ⟨VacuumListing.relax (L.budget m) hs.high le_rfl hs.reserve, ?_⟩
  intro O z
  have hV : Lives R.alloy.B.bake N m p V := ((R.T.sticks N p).prices m (Nat.zero_le _) hm.le).1
  have hpath : V.path = R.alloy.B.kin.path N m := by rw [hV.path,R.alloy.B.bases]
  rw [hpath,hV.clip]
  exact ((congr_fun (R.makes.wilson.steps N p m hm).1 z).trans (hs.integral O z)).trans
    (hs.assembled O z)

end YM.Integration.WilsonLimitConstruction.FundedCensusVacuum
end

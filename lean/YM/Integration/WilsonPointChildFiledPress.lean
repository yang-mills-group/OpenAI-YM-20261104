import YM.Integration.WilsonPointChildPressCalendar
import YM.Integration.WilsonNeutralPointCourse

/-! The original one-residue signed press on the normalized declared
    singleton, simultaneously at every cutoff and every digit itinerary. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildFiledPress
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildFreight WilsonPointChildPressIncome WilsonPointChildPressCalendar WilsonNeutralPointCourse
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {d D:ℕ}

structure Tour (R:Run G)(k:ℕ) where
  cutoff:ℕ
  live:k≤cutoff
  digit:∀j,Site (R.family.S.block j)

abbrev width (R:Run G)(i:ℕ):ℝ:=(Primer.FamilyWindow R.family).width (R.family.path.levels.clock.J i)

theorem scaled {j t:ℕ}{P:Flight j t}{K:KernelChoices}(H:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
    (a:hue G)(Y:Anthem D G)(hl:2≤P.L.val)(d u:ℕ)(f:Studio D)(x:Site P.L):
    WilsonPointChildPressIncome.step P ρ H W h a Y hl d u f x =
    WilsonNeutralPointMatrix.child P H W a ρ h hl d u x Y f:=by
  funext e r
  unfold WilsonPointChildPressIncome.step WilsonNeutralPointMatrix.child Sierra.enterStep Wine.stamp
  simp only [Pi.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact smul_comm _ _ _

theorem original (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (o:Loc G 1)(simple:G.Simple){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    (e r:ℕ):∀ᶠk:ℕ in atTop,∀(A B:Tour R k→ℕ→ℝ),
    (∀z j,k≤j→j≤z.cutoff→0≤A z j)→(∀z j,k≤j→j≤z.cutoff→1≤B z j)→
    (∀z j,k≤j→j<z.cutoff→∀b:Letter (R.family.labels.level d),∀p:Studio D,∀l≤e,∀m,
      Knoxville (fame _) 0 (0,o) (filed R wood a depth z.digit z.cutoff (j+1) b p l m) (A z (j+1)*‖p‖))→
    (∀z j,k≤j→j<z.cutoff→∀b:Letter (R.family.labels.level d),∀p:Studio D,∀l≤e,∀m,
      Knoxville (fame _) (width R (j+1)) (0,o) (filed R wood a depth z.digit z.cutoff (j+1) b p l m) (B z (j+1)*‖p‖))→
    ∃c:ℝ,∃v:ℕ,0≤c∧∀z:Tour R k,∀j,k≤j→j<z.cutoff→∀b:Letter (R.family.labels.level d),∀p:Studio D,
      Knoxville (fame _) (width R j) (0,o)
        (forward R wood a z.digit z.cutoff j (filed R wood a depth z.digit z.cutoff (j+1)) b p e r)
        (c*(max 1 (ageZ (R.family.path.levels.clock.hatBeta j)))^v*
          (((1+A z (j+1))*(B z (j+1))^((width R j/(R.family.S.block j).val)/width R (j+1)))*‖p‖)):=by
  filter_upwards [WilsonPointChildPressCalendar.original R wood simple granted e] with k registered
  intro A B ga gb low high
  let X:=Tour R k × Letter (R.family.labels.level d)
  let W:=estate X R wood k
  let C:Pin W.scrolls:=⟨fun z=>z.1.cutoff,fun z=>z.1.live⟩
  let T:=fun z:Turn C=> filed R wood a depth z.a.1.digit z.a.1.cutoff (z.b+1) z.a.2
  obtain ⟨c,v,cn,paid⟩:=registered X C a _ d d e r le_rfl o T
    (fun z=>A z.a.1 (z.b+1)) (fun z=>B z.a.1 (z.b+1))
    (fun z=>ga _ _ (z.zone.trans (Nat.le_succ z.b)) z.head)
    (fun z=>gb _ _ (z.zone.trans (Nat.le_succ z.b)) z.head)
    (fun l hl m z p=>low _ _ z.zone z.head _ p l hl m)
    (fun l hl m z p=>high _ _ z.zone z.head _ p l hl m)
  refine ⟨c,v,cn,?_⟩
  intro z j kj jN b p
  let w:Turn C:=⟨⟨(z,b),j,kj⟩,jN⟩
  have wr:=paid w p (z.digit j)
  rw [scaled] at wr
  exact wr

end YM.Integration.WilsonPointChildFiledPress

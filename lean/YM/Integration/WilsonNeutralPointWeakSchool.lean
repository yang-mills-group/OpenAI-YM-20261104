import YM.Integration.WilsonEmittedPointedRequests
import YM.Integration.WilsonNeutralPointWeakTransfer
import YM.Integration.WilsonWindowFormalAnnouncement
import YM.FormalBulk08.Elm.Knoll

/-! The polynomial moment ledger is bought before the cutoff and the whole
site itinerary, on the actual selected Wilson clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointWeakSchool
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Quire Palm Grail Chapel Borough Sable Tundra Aster Clover Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels WilsonNeutralPointWeakLedger
open PhysicalNext.Repeat.Legato Next.Foundations
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d D E w:ℕ}(R:Run G)

abbrev campus (X:Type)(wood:∀i,Lodge ((R.family.path.levels.clock.op i 0).patch))(k:ℕ):Lab G R.family.path.levels.clock.kernel X:=
  register G R.family.path.levels.clock.kernel
    (⟨fun _=>R.family.path.levels,fun _=>rfl,fun _=>wood⟩:Empire G R.family.path.levels.clock.kernel X)
    (Primer.FamilyWindow R.family) (fun _=>k) (fun _=>lyre R.family.path.levels)

private def paid (d D e r l u j:ℕ):Prop:=
  let A:=R.family.path.levels
  ∀(o:Loc G 1)(S:Lodge (A.clock.op j 0).patch),∃b:ℝ,0≤b ∧ b≤ageZ (A.clock.hatBeta j) ∧
    ∀(P:Flight (A.clock.J (j+1)) (A.clock.J j))(V:Lodge P.patch)(hp:P.patch=(A.clock.op j 0).patch),
      hp ▸ V=S → ∀x:Site P.L,Admission R.family.path.levels.clock.kernel (R.family.labels.level d) o u P V x e r l D (Mulct P.L) b

private theorem tariff (hD:d<D)(strong:WilsonNeutralPointForecast.Filed R.kit)
    (weak:WilsonNeutralPointWeakForecast.Filed R.kit):
    ∀ᶠj:ℕ in atTop,∀(e:Fin (E+1))(r:Fin (d+E+1))(l:Fin (d+1)),
      paid R d D e r l (max w ((d+1)*(d+1))) j:=by
  apply Filter.eventually_all.mpr; intro e
  apply Filter.eventually_all.mpr; intro r
  apply Filter.eventually_all.mpr; intro l
  filter_upwards [WilsonEmittedPointedRequests.original R d D e r l w hD strong weak] with j price
  obtain ⟨admit,buy⟩:=price
  intro o S
  obtain ⟨_,b,_,hb,_,ticket⟩:=buy o 0 S
  rw [show R.family.path.levels.clock.kernel=R.metals.p.kernel from R.alloy.B.valid.kernel]
  refine ⟨b,ticket.1,hb,fun P V hp hv x=>⟨?_⟩⟩
  intro T hvT B paidT priceT A hA normT hL
  exact ticket.2 P V hp hv T hvT B paidT priceT A hA normT x hL

theorem original (hD:d<D)(wood:∀j,Lodge ((R.family.path.levels.clock.op j 0).patch))
    (strong:WilsonNeutralPointForecast.Filed R.kit)(weak:WilsonNeutralPointWeakForecast.Filed R.kit):
    ∀ᶠk:ℕ in atTop,∀(X:Type)(C:Pin (campus R X wood k).scrolls)(o:Loc G 1)
      (digit:∀i:Turn C,Site ((campus R X wood k).liftF i).L),
      Ledger R.family.path.levels.clock.kernel (R.family.labels.level d) o
        (graded (campus R X wood k).liftF ((campus R X wood k).trail C.N))
        (campus R X wood k).liftU digit E d D (max w ((d+1)*(d+1))) (tide C) (Turn.rad (1/2:ℝ)):=by
  obtain ⟨k,ready⟩:=eventually_atTop.1 (tariff (E:=E) (w:=w) R hD strong weak)
  filter_upwards [eventually_ge_atTop k] with k' hk X C o digit
  let U:=campus R X wood k'
  refine ⟨(by nlinarith [Nat.le_max_right w ((d+1)*(d+1))]),?_⟩
  intro e he r hr l hl
  have available (i:Turn C):=ready i.b (hk.trans i.zone)
    (⟨e,Nat.lt_succ_of_le he⟩:Fin (E+1)) (⟨r,Nat.lt_succ_of_le hr⟩:Fin (d+E+1))
    (⟨l,Nat.lt_succ_of_le hl⟩:Fin (d+1)) o (wood i.b)
  choose b hn cap pay using available
  refine ⟨b,⟨1,1,zero_le_one,fun i=>?_⟩,fun i=>?_⟩
  · simp only [one_mul,pow_one,abs_of_nonneg (hn i)]
    exact (cap i).trans (le_max_right ..)
  · let P:=graded U.liftF (U.trail C.N) i
    rw [show Turn.rad (1/2:ℝ) i=Mulct P.L from (mulct_step R.family.S i.b).symm]
    exact pay i P (U.liftU i) rfl rfl (digit i)

end YM.Integration.WilsonNeutralPointWeakSchool
end

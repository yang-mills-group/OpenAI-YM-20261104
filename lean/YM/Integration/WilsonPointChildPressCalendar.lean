import YM.Integration.WilsonPointChildPressIncome
import YM.Integration.WilsonWindowFormalAnnouncement
import YM.FormalBulk08.Elm.Knoll

/-! The original press prices a whole family of birth dates and child
    itineraries with one gross expense. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildPressCalendar
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildFreight WilsonPointChildPressIncome
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {K:KernelChoices} {X:Type}

abbrev estate (X:Type)(R:Run G)(wood:∀j,Lodge ((R.family.path.levels.clock.op j 0).patch))(k:ℕ):Lab G R.family.path.levels.clock.kernel X:=
  register G R.family.path.levels.clock.kernel
    (⟨fun _=>R.family.path.levels,fun _=>rfl,fun _=>wood⟩:Empire G R.family.path.levels.clock.kernel X)
    (Primer.FamilyWindow R.family) (fun _=>k) (fun _=>lyre R.family.path.levels)

def bill (U:Lab G K X)(C:Pin U.scrolls)(ρ:ChartRatio G)(a:hue G)(E:ℕ):Prop:=
  ∀(D d u e r:ℕ),e≤E→∀(o:Loc G 1)(T:Turn C→Anthem D G)(A B:Turn C→ℝ),
    (∀i,0≤A i)→(∀i,1≤B i)→
    (∀j≤e,∀m,∀i:Turn C,∀p:Studio D,Knoxville (fame _) 0 (0,o) (T i p j m) (A i*‖p‖))→
    (∀j≤e,∀m,∀i:Turn C,∀p:Studio D,Knoxville (fame _) (U.stub i) (0,o) (T i p j m) (B i*‖p‖))→
    ∃c:ℝ,∃v:ℕ,0≤c ∧ ∀(i:Turn C)(p:Studio D)(x:Site (U.liftF i).L),
      Knoxville (fame _) (U.sail i) (0,o) (WilsonPointChildPressIncome.step (graded U.liftF (U.trail C.N) i)
        ρ (U.liftU i) (Lab.instory ρ a U C.N i.ups) (U.liftH i) a (T i) (Elm.growL (U.V i.a) i.b) d u p x e r)
        (c*((tide C).day i)^v * (income U.liftF U.stub U.sail A B i*‖p‖))

theorem on_course (W:Lab G K X)(C:Pin W.scrolls)(ρ:ChartRatio G)(a:hue G)(E:ℕ)
    (use:W.Use ρ E)(localRatio:LocalRatio ρ)(simple:G.Simple):bill W C ρ a E:=by
  intro D d u e r cap o T A B ha hb low top
  have receipts:=Elm.grasp use C C (fun _=>le_rfl) localRatio simple a
  obtain ⟨H,⟨c,q,cn,fit⟩,positive,paid⟩:=WilsonPointChildPressIncome.original receipts (o:=o) T A B ha hb
    (fun i=>(Elm.growL (W.V i.a) i.b)) d u e r cap low top
  refine ⟨c,q,cn,fun i p x=>(paid i p x).mono ?_⟩
  apply mul_le_mul_of_nonneg_right ((le_abs_self (H i)).trans (fit i))
  exact mul_nonneg (mul_nonneg (add_nonneg zero_le_one (ha i))
    (Real.rpow_nonneg (zero_le_one.trans (hb i)) _)) (norm_nonneg _)

/-- The original activation depends only on the booked order. The cutoff
    can then be an arbitrary coordinate of X and the same constants cover
    every remaining digit, phase and held point in that family. -/
theorem original (R:Run G)(wood:∀j,Lodge ((R.family.path.levels.clock.op j 0).patch))(simple:G.Simple){U:ℕ→ℕ}
    (granted:WilsonWindowFormalPurchase.Canonical U R.kit)(E:ℕ):
    ∀ᶠk:ℕ in atTop,∀(X:Type)(C:Pin (estate X R wood k).scrolls)(a:hue G),
      bill (estate X R wood k) C R.metals.O a E:=by
  let V:=R.family.path.levels
  have grows:Tendsto (fun k:ℕ=>V.clock.J (k+1)) atTop atTop:=V.fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [grows.eventually_ge_atTop (E+5)] with k active X C a
  let W:=estate X R wood k
  have post:Poster (Primer.Noise R.family) Spigot.herald R.family.labels.level R.family.params (chart G) W (E+5):=
    presold simple (W:=Primer.FamilyWindow R.family) (U:=W.toEmpire)
      (fun _=>(WilsonWindowFormalAnnouncement.on_run R granted).power) W.neck (by omega) (fun _=>active)
  rw [show R.metals.O=chart G from granted.1]
  exact on_course W C _ a E (post.vac E (by omega)) (chart_ok G) simple

end YM.Integration.WilsonPointChildPressCalendar

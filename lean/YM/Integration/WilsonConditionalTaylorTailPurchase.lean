import YM.Integration.WilsonConditionalTaylorCalendar
import YM.Integration.WilsonConditionalTaylorLabels
import YM.Integration.WilsonConditionalTaylorCaliperPayment
import YM.Integration.FVA1Physical.Wilson.FluctuationFieldRows
import YM.Integration.FVA1Physical.Wilson.SceneReadout

/-! A true pre-launch numerical purchase of *each omitted coefficient* of
the nonlinear fluctuating marked bank. The requests precede every future
period, chosen forest and tested physical field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorTailPurchase

open Function Filter Finset Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule RGComparison.Core16.Spool
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open MSbar MSbar.Lis MSbar.Heath MSbar.Heath.Cottage MSbar.Mosaic MSbar.Bulk MSbar.Bakery MSbar.Bakery.Film
open MSbar.Heath.Stock
open MSbar.Cacao MSbar.Rolling MSbar.Whisk MSbar.Midpoint Tree Pressure Push.Uniform Exterior
open WilsonConditionalTaylorThreshold WilsonConditionalTaylorCalendar WilsonConditionalTaylorLabels
open WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology BigOperators

variable {G : Gauge} (V : Voice G) (cle : Clear G V) (simple : G.Simple)

abbrev Request (G : Gauge) := Entry G × ℕ × ℕ × ℕ × ℕ × ℕ × Bool

def fare (t : Request G) (_price : MapPrices) : Fare :=
  fun H H' P K=> let ⟨e,q,s,L,d,h,part⟩:=t
    if branch:P.Branches K G then
      (eventually_atTop.mp (fluctuation_field_rows (packet e) V cle (chart G) (chart_ok G) simple
        H H' P K branch (q+2) s 0 L part (Nat.cast_nonneg d) (loss_pos h))).choose else 0

def dues := @Paid G (atlas (fare V cle simple))

theorem prepaid (s : Sheet G) (M : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@dues G V cle simple) s M :=
  WilsonConditionalTaylorThreshold.prepaid _ s M

theorem rows (R : Run G) (u : G.ColorIndex) (frame : R.metals.O=chart G)
    (invoice : vacuumInvoice u V R.metals R.rolls R.alloy R.kit) (finance : dues V cle simple R.kit)
    (e : Entry G) (q s L d h : ℕ) (part : Bool) (hs : 6 ≤ s) :
  ∀ᶠ k : ℕ in atTop, ∀ N n, k≤N →
    (∃ S : Scene R.family.path.levels n (q+2), Realized R.alloy.B.kin N n k (q+2) (Lis.sun G u) S) ∧
    ∀ (S : Scene R.family.path.levels n (q+2)) (scene : Realized R.alloy.B.kin N n k (q+2) (Lis.sun G u) S),
      ∀ j (kj:k≤j) (hi:j<N),
        let F:=(scene.step j hi kj).choose
        let t:=(scene.step j hi kj).choose_spec.choose
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F t
        let y:=R.family.path.levels.clock.hatBeta (j+1)
        ∀ (b : Site A.f) (Z : Positions (Primary A.c G)), ‖A.fClock • Z‖ ≤ d*room y →
          ∀ (o : ↥e.2→Site A.f), (∀ t : Slice (packet e), separation b (legs (packet e) o t).1≤L*closeN y) →
          ∀ i≤q+2, |PowerSeries.coeff i (bulkColumn A R.metals.O (A.fClock•Z)
            (jointFieldBank (packet e) A o part) (q+2))| ≤ y^(loss h) := by
  obtain ⟨docket,_⟩:=docket_of_invoice simple R u V invoice
  let ask : Request G:=⟨e,q,s,L,d,h,part⟩
  obtain ⟨start,bill⟩:=eventually_atTop.mp (read R (fare V cle simple) finance ask)
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  filter_upwards [docket.purse s (q+2) (q+2+4) hs (by omega) (by omega),eventually_ge_atTop start]
    with k budget late N n kN
  obtain ⟨existsScene,held⟩:=budget N n kN
  refine ⟨existsScene,?_⟩
  intro S scene j kj hi F t A y b Z size o near i cap
  let H:=R.family.path.levels.params j;let H':=R.family.path.levels.params (j+1)
  let x:=R.family.path.levels.clock.hatBeta j
  let P:=A.S.patch;let K:=A.S.kernel
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j hi simple (invoice.1 growth).sees
    (fun i=>invoice.2.1 _ _ (R.alloy.B.valid.pays i) _ (step_paid R.alloy.B.a i))
  have branch:P.Branches K G:=season.bends.1
  have cost:=bill j (late.trans kj) n
  change (if w:P.Branches K G then (eventually_atTop.mp (fluctuation_field_rows (packet e) V cle (chart G)
    (chart_ok G) simple H H' P K w (q+2) s 0 L part (Nat.cast_nonneg d) (loss_pos h))).choose else 0) ≤ x at cost
  rw [dif_pos branch] at cost
  have grant:=(eventually_atTop.mp (fluctuation_field_rows (packet e) V cle (chart G) (chart_ok G) simple
    H H' P K branch (q+2) s 0 L part (Nat.cast_nonneg d) (loss_pos h))).choose_spec x cost A b rfl rfl season
  dsimp only at grant
  have height:tip G P.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  rw [height] at grant
  have je:=kj.trans (Nat.le_succ j)
  have trend:=(scene.budget (j+1) hi je).1
  have wedge:=(held S scene).2.2 (j+1) je hi
  have bought:=grant trend.bond trend.plane wedge (A.fClock•Z) size o near i cap
  have ha : 0≤αm y:=by unfold αm hatW Alto.flurry; positivity
  rw [frame,normalizedRows_read]
  exact Bout.looks ha bought

end YM.Integration.WilsonConditionalTaylorTailPurchase
end


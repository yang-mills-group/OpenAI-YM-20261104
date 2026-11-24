import YM.Integration.WilsonMatrixOriginalFiledCovariance
import YM.Integration.WilsonMatrixOriginalFirstSignedPanel

/-! The purchased two-site Ward detector on the varying labels actually filed at every cutoff. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalFiledPanel
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonLimitConstruction WilsonMatrixOriginalSignedPanel WilsonInvariantActionCalibratedColumn
open WilsonMatrixOriginalSignedReading WilsonMatrixOriginalRealFields
open private dilate_real from YM.Integration.WilsonMatrixOriginalSignedPanel
open private packet_real from YM.Integration.WilsonMatrixOriginalFirstSignedPanel
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G) (L : Layout F)
    {U : Filter (ℕ × ℕ)} [U.NeBot] (chosen : U ≤ L.lens)

def Value (a b : ℝ → R.family.label 4) (χ : ℂ →L[ℝ] ℝ) (φ : Test 2)
    {r : ℝ} (hr : 0 < r) (z : ℕ × ℕ) : ℝ :=
  signed R (atRef L 4 r z (a r)) (atRef L 4 r z (b r)) χ (dilate hr φ) z.1 z.2

def Filed (a b : ℝ → R.family.label 4) (v : ℝ → S.Field 4) (φ : Test 2) (c : ℂ)
    (χ : ℂ →L[ℝ] ℝ) : Prop :=
  0 < |χ c| ∧ ∀ᶠ r in trail, ∀ hr : 0 < r,
    let z := χ (tested (J r 4 (stepField R.family)) (v r) r φ)
    |χ c|/2 < |z| ∧ Tendsto (Value F L a b χ φ hr) U (𝓝 z) ∧
      ∀ᶠ s : ℕ × ℕ in U, |χ c|/4 < |Value F L a b χ φ hr s|

include chosen in
theorem purchased (simple : G.Simple) {A : ℝ → change S 4} {δ g : ℝ → ℝ}
    (same : ∀ᶠ r in trail,J r 4=A r) (cal : TendC F A δ) (coupling : Coupling G g)
    (a b : ℝ → R.family.label 4) (v : ℝ → S.Field 4) (φ : Test 2)
    (true_test : ∀ x,φ x = ((φ x).re : ℂ)) (c : ℂ) (χ : ℂ →L[ℝ] ℝ)
    (detected : Lower (f:=f) J v φ c χ)
    (alive : ∀ᶠ r in trail,R.family.ref 4 ≤ L.level r)
    (labels : ∀ᶠ r in trail,master L 4 r (a r)=J r 4 (stepField R.family) ∧
      master L 4 r (b r)=v r) :
    Filed (U:=U) F J L a b v φ c χ := by
  refine ⟨detected.2.1,?_⟩
  filter_upwards [detected.2.2,alive,labels,WilsonMatrixOriginalActionReality.ward F J simple same cal coupling]
    with r gap live name honest
  intro hr
  let cut (N _ : ℕ) : Fin (N+1) := ⟨N,Nat.lt_succ_self N⟩
  have first : centering S 4 (S.project 4 (realLabel (R:=R) (S.representative 4 (master L 4 r (a r))))) =
      centering S 4 (master L 4 r (a r)) := by rwa [name.1]
  have actual := WilsonMatrixOriginalFiledCovariance.filed F L chosen cut φ hr
    (dilate_real φ true_test hr) live (a r) (b r) χ first
  rw [name.1,name.2] at actual
  have margin := (gap hr).1
  refine ⟨margin,actual,?_⟩
  exact ((continuous_abs.tendsto _).comp actual).eventually
    (lt_mem_nhds (lt_trans (show |χ c|/4 < |χ c|/2 by linarith [detected.2.1]) margin))

variable {H : (Bel R.family.book).Hierarchy} (lead : Leading F J)
    (paid : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple : G.Simple)
    {ρ:ℝ} {T:Campaign R} {P:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple ρ P)
    (pace:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (hB:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {u₀:Filter (ℕ×ℕ)} (bank:Mantle F u₀) (E:Services R.family f S) (pegs:Pegs bank L)
local notation "β" => R.family.path.levels.clock.hatBeta

include lead paid simple funded pace hB level chosen E pegs in
theorem original {A:ℝ→Spin.change S 4} {δ g:ℝ→ℝ} (same:∀ᶠr in trail,J r 4=A r)
    (cent:∀ᶠr in trail,AlignV F.room.kernel F.sector H (A r)) (cal:TendC F A δ) (coupling:Coupling G g) :
    ∃ (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
      (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
      (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ),
      let φ := WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
      let v := (Bel R.family.book).project 4 v₀
      let b := fun r => homogeneous F J Z r 4 v
      let c := tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
      (χ=Complex.reCLM ∨ χ=Complex.imCLM) ∧
      Filed (U:=U) F J L (fun r => deposit r (stepField R.family)) (fun r => deposit r (freeInput F J Z 4 r v)) b φ c χ ∧
      (∀ᶠ r in trail,∀u:RG17.Free R.family 4,master L 4 r (deposit r u)=J r 4 u ∧
        ∀N n,L.level r ≤ N→quota R.family 4 (L.level r) N n (atRef L 4 r (N,n) (deposit r u)) ≤
          R.family.S.a (L.level r)^4*(β (L.level r)^e*‖u‖)) := by
  obtain ⟨D,j,w,hs,e,deposit,χ,detected,market,regular⟩ :=
    WilsonMatrixOriginalFirstSignedPanel.original F J Z lead paid simple funded pace L hB level chosen bank E pegs
      same cent cal coupling
  refine ⟨D,j,w,hs,e,deposit,χ,detected.1,?_,market⟩
  apply purchased F J L chosen simple same cal coupling _ _ _ _
    (packet_real w hs (test D j) (fun _ => rfl)) _ χ detected
    (pegs.level.growing.eventually_ge_atTop (R.family.ref 4))
  filter_upwards [regular 0 1 one_pos] with r price
  exact ⟨price.1,price.2.1⟩

end YM.Integration.WilsonMatrixOriginalFiledPanel

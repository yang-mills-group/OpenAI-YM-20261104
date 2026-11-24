import YM.Integration.WilsonReceivedSourceGross
import YM.Integration.WilsonJointAxialWindow
import YM.Integration.WilsonReceivedAxialCurrency
import YM.Integration.WilsonRegisteredAxialChart
import YM.Integration.WilsonRegisteredAxialRoom

/-! All occupied faces of a genuine Wilson post on arbitrary placements
receive one healthy common angle. The larger collar is purchased before the
top cutoff and period; the original short-support cutoff remains unchanged. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonJointAxialRoster
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare
open scoped Classical BigOperators Topology

def invoice (c p : ℕ) := (2*c+1)*(p+4)

def plaquettes {n' : Side} {V : Type} [Fintype V] (o : V → Site n') (H : ℕ) :
    Finset (Face (Per n')) := Finset.univ.biUnion fun v => WilsonAxialWindow.cells (o v) H

private theorem enlarged {G : Gauge} (R : Run G) {i c p : ℕ}
    (one : 1 ≤ Real.log (R.family.path.levels.clock.hatBeta i)) :
    let B := R.family.path.levels.clock.coverSize i
    let b := WilsonDegreeFourInheritedRange.height R p i
    let h := b*(4*B+2)+2*B+1
    c*(2*h)+h ≤ radius R (invoice c p) 1 i := by
  intro B b h
  let t := 2*c+1
  let s := Real.log (R.family.path.levels.clock.hatBeta i)
  have lo : 0 ≤ s := zero_le_one.trans one
  have high : (b:ℝ) ≤ ((p:ℝ)+2)*s+1 := by
    dsimp [b,WilsonDegreeFourInheritedRange.height]
    push_cast
    exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity) lo)).le
  have larger := Nat.le_ceil (((invoice c p+2 : ℕ):ℝ)*s)
  change _ ≤ (WilsonDegreeFourInheritedRange.height R (invoice c p) i:ℝ) at larger
  have num : t*(b+1) ≤ WilsonDegreeFourInheritedRange.height R (invoice c p) i := by
    apply (Nat.cast_le (α:=ℝ)).mp
    apply le_trans _ larger
    change ((t*(b+1):ℕ):ℝ) ≤ (((t*(p+4)+2:ℕ):ℝ))*s
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left high (Nat.cast_nonneg t : (0:ℝ)≤t),
      mul_le_mul_of_nonneg_left one (Nat.cast_nonneg t : (0:ℝ)≤t),lo]
  change _ ≤ 1 + WilsonDegreeFourInheritedRange.height R (invoice c p) i*(4*B+2) + 2*B
  calc
    c*(2*h)+h = t*h := by dsimp only [t];ring
    _ ≤ t*((b+1)*(4*B+2)) := Nat.mul_le_mul_left _ (by dsimp only [h];rw [Nat.add_mul];omega)
    _ = t*(b+1)*(4*B+2) := (Nat.mul_assoc ..).symm
    _ ≤ _ := (Nat.mul_le_mul_right (4*B+2) num).trans (by omega)

def opening {G : Gauge} (R : Run G) (simple : G.Simple) {η : ℝ} {T : Campaign R}
    {W : Campaign.Pillars R T} (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (c n q : ℕ) {ε : ℝ} (ep : 0 < ε) : ℕ :=
  max (WilsonReceivedSourceGross.opening R simple)
    (max ((eventually_atTop.mp (WilsonReceivedAxialCurrency.price R simple funded n q ep)).choose)
      (max ((eventually_atTop.mp
        ((Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop 1)).choose)
        (max ((eventually_atTop.mp (WilsonRegisteredAxialRoom.torus R simple (invoice c (q+2*n)) 1)).choose)
          ((eventually_atTop.mp (WilsonRegisteredAxialChart.fit R simple slow J clear
            (invoice c (q+2*n)) 0)).choose+1))))

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "a" => ((Ψ i).p.supportExponent+1+1)
local notation "fee" => ((Spill.allOver (Ψ i).p)^(order+shelf+1)*Ω)

local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (order+shelf+2)

include course cut in
theorem selected (simple : G.Simple) {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (late : opening R simple funded slow J clear (Fintype.card V) n q ep ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let b := WilsonDegreeFourInheritedRange.height R (q+2*n) i
    ∀ U : Config G (R.family.side i per),U ∈ House.chilly (plaquettes (placed).origin H) τ →
      let ξ := WilsonJointAxialWindow.direction (placed).origin
          ((WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1) J axes r U;
        0 ≤ r ∧ r ≤ 1 ∧ (∀ e,‖ξ e‖ ≤ (Ψ i).p.threshold) ∧
        (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support (R.family.side i per),
          Healthy (Ψ i).p.threshold Y (increment 1 (z • ξ))) ∧
        (∀ t j, ((lamps).mode j).val.Nonempty → coverNumber (Ψ i).p.B ((lamps).ground j)<b →
          (lamps).nominal t j U = (lamps).nominal t j (increment 1 (r • ξ))) ∧
        ∀ (t : Wallet actors) (s : (Stock.census V).Mode),s.val.Nonempty →
          Poly.toll P.w s*‖(bare lamps t U).part s-(bare lamps t (increment 1 (r • ξ))).part s‖ ≤
            ε*(regulatorRun R.family N per i)^q := by
  intro H r τ b U cold
  obtain ⟨lg,lr⟩ := max_le_iff.mp late
  obtain ⟨lc,lr'⟩ := max_le_iff.mp lr
  obtain ⟨ll,lf⟩ := max_le_iff.mp lr'
  obtain ⟨ltor,lchart⟩ := max_le_iff.mp lf
  have cal := (eventually_atTop.mp
    (WilsonRegisteredAxialChart.fit R simple slow J clear (invoice (Fintype.card V) (q+2*n)) 0)).choose_spec
  have back : i-1+1=i := by omega
  have fit := cal (i-1) (Nat.le_sub_one_of_lt lchart) N per (by rw [back];exact cut.le)
  rw [back] at fit
  obtain ⟨rp,weak,chart,logarithm,rad,stay⟩ := fit
  have point : (Ψ i).p = R.family.path.levels.budget i := (course.1.walk i hi cut.le).truep.point
  have physicalPoint : (Ψ i).p = (R.family.path.rep N per i).p :=
    point.trans (R.makes.wilson.represents N per i cut.le).vac.symm
  let h := b*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
  have logs := (eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop 1)).choose_spec i ll
  have room := (eventually_atTop.mp
    (WilsonRegisteredAxialRoom.torus R simple (invoice (Fintype.card V) (q+2*n)) 1)).choose_spec i ltor per
  change 10*H < _ at room
  have smallRoom : 2*H < (R.family.side i per).val := by omega
  have geometry : Fintype.card V*(2*h)+h ≤ H := by
    dsimp only [h]
    rw [point]
    exact enlarged R logs
  have allCold (v : V) : U ∈ House.chilly (WilsonAxialWindow.cells ((placed).origin v) H) τ := by
    intro f mem
    exact cold f (Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,mem⟩)
  let ξ := WilsonJointAxialWindow.direction (placed).origin
          ((WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1) J axes r U
  obtain ⟨uniform,healthy,read⟩ := WilsonJointAxialWindow.selected (p:=(Ψ i).p) (placed).origin J clear
    axes h H geometry smallRoom weak rp U allCold chart (by simpa only [physicalPoint] using logarithm)
    (by simpa only [physicalPoint] using rad) stay
  have short (t : Wallet actors) (j) (marks : ((lamps).mode j).val.Nonempty)
      (tiny : coverNumber (Ψ i).p.B ((lamps).ground j)<b) :
      (lamps).nominal t j U = (lamps).nominal t j (increment 1 (r • ξ)) := by
    obtain ⟨v,hv⟩ := marks
    apply read v ((lamps).legal t j)
    intro x hx
    have dist := Corona.extent _ (Ψ i).p.B ((lamps).roots j v hv) hx
    exact dist.trans_lt (Nat.lt_succ_of_le
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ tiny.le) _))
  have r1 : r ≤ 1 := by nlinarith only [stay,rp.le,mul_nonneg (sub_nonneg.mpr clear.cost) rp.le]
  refine ⟨rp.le,r1,uniform,healthy,short,?_⟩
  intro t s marks
  obtain ⟨v,hv⟩ := marks
  have Gs := WilsonReceivedSourceGross.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces
    grades order shelf seats physical P simple lg pass hospital narrow load
  have hn : 0 ≤ fee := mul_nonneg (pow_nonneg (zero_le_one.trans (Spill.allOver_ge _)) _)
    P.issued.Waffle.paysAbove.le
  have ha : 0 ≤ a := by linarith only [(Ψ i).p.exponent_pos]
  have diff := WilsonReceivedAxialExtension.changed lamps P.issued.earning.positive ha Gs.1
    t s v hv b U (increment 1 (r • ξ))
    (fun j eq h => short t j (eq.symm ▸ ⟨v,hv⟩) h)
  have pay := (eventually_atTop.mp (WilsonReceivedAxialCurrency.price R simple funded n q ep)).choose_spec
    i lc N per cut a (by rw [←physicalPoint];linarith) fee hn Gs.2
    (Poly.toll P.w s*‖(bare lamps t U).part s-(bare lamps t (increment 1 (r • ξ))).part s‖)
  exact pay (by simpa only [mul_assoc] using diff)
include course cut in
theorem original (simple : G.Simple) {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (late : opening R simple funded slow J clear (Fintype.card V) n q ep ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let b := WilsonDegreeFourInheritedRange.height R (q+2*n) i
    ∀ U : Config G (R.family.side i per),U ∈ House.chilly (plaquettes (placed).origin H) τ →
      ∃ ξ : Directions G (R.family.side i per),0 ≤ r ∧ r ≤ 1 ∧ (∀ e,‖ξ e‖ ≤ (Ψ i).p.threshold) ∧
        (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support (R.family.side i per),
          Healthy (Ψ i).p.threshold Y (increment 1 (z • ξ))) ∧
        (∀ t j, ((lamps).mode j).val.Nonempty → coverNumber (Ψ i).p.B ((lamps).ground j)<b →
          (lamps).nominal t j U = (lamps).nominal t j (increment 1 (r • ξ))) ∧
        ∀ (t : Wallet actors) (s : (Stock.census V).Mode),s.val.Nonempty →
          Poly.toll P.w s*‖(bare lamps t U).part s-(bare lamps t (increment 1 (r • ξ))).part s‖ ≤
            ε*(regulatorRun R.family N per i)^q := by
  intro H r τ b U cold
  exact ⟨WilsonJointAxialWindow.direction (placed).origin
          ((WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1) J axes r U,
    selected R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P
    simple funded slow J clear axes q ep late pass hospital narrow load U cold⟩

end YM.Integration.WilsonJointAxialRoster

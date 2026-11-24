import YM.Integration.WilsonCoveredOrdinaryRestored
import YM.Integration.WilsonReceivedCloseOrdinaryRoster

/-! The same realized close trail with its complete physical ordinary table and its matching named covered program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseFoldedOrdinary
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


local notation "J₀" => Stock.census V
local notation "width" fund:max expo:max => fund*((g b)⁻¹)^expo
local notation "pow₀" a:max d:max q:max => q+d*a+1+a
local notation "Pupil" i:max mi:max L:max =>
  Oak.student (n:=per) (i:=i) R hk D Q π Γ books mi (L).op (L).lesson ahead actors (L).model order (L).voter
local notation "teacher" i:max mi:max L:max x:max => Air.craft (Pupil i mi L)
  (fun s=>((Pupil i mi L) s).paint x) grades (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "bank" i:max L:max x:max => Air.craft (L).model (fun s=>((L).model s).paint x)
  grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "Covered" => ∀i:ℕ,i ≤ b → Wallet actors → Stationary.Link G (R.family.side i per) → ℕ → Poly J₀
local notation "Walk" start:max i:max mi:max ib:max L:max =>
  WilsonReceivedCloseHistory.Trail (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source start i mi (read i ib) L

def Match (start:P b mb source) (K:Covered) : Prop :=
  ∀ (i:ℕ)(mi:m ≤ i)(ib:i ≤ b)(L:P i mi (read i ib)),Walk start i mi ib L → 
    ∀ (x:Wallet actors)(A:Stationary.Link G (R.family.side i per))(l:ℕ),l ≤ order → 
    K i ib x A l=Air.discharge (teacher i mi L x) l (Stationary.arm G (R.family.side i per) 1 A)

/-- Each physical subset, independent finite log and independent folded ordinary value use
the same actual insertion, the same coarse field, and the same radii after re-inscription. -/
def Heard (start:P b mb source) (top:b<N) (K:Covered) (span:ℕ) (H cap:ℝ)
    (active:Finset V) (a d q:ℕ) (U ε:ℝ) : Prop :=
  ∀i (ib:i ≤ b)(mi:m ≤ i),∃ L:P i mi (read i ib), Walk start i mi ib L ∧
    (∀s:(J₀).Mode,s.val ⊆ active → (Poly.toll L.w s)⁻¹ ≤ (width U d)^s.val.card) ∧
    ∀ (x:Wallet actors) (F:Forest (move i).ratio) (tag:(move i).Choices)
      (A:Stationary.Link G (R.family.side i per)) (z:ℝ),
      let B:=R.family.path.levels.budget i
      let angle:=Stationary.arm G (R.family.side i per) 1 A
      |z| ≤ |H| *(Real.log (R.family.path.levels.clock.hatBeta i))^span*((B.B:ℝ)^2*B.threshold)/(g (i+1)) → 
      (∀e,‖Exterior.collect G angle e‖ ≤ cap* |z|) → 
      let U₀:=Integral.sample (g (i+1)) angle
      flags (Ψ i).p.threshold U₀=∅ → 
      let Y:=(((Ψ i).eval U₀:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i ((read i ib) x) U₀
      let W:=Bulk.Fk ((RunFormalChain.fromRun R).step N i per (ib.trans_lt top)) F tag (bank i L x) angle order
      let folded:=WilsonCoveredOrdinaryPolynomial.evaluated order (K i ib x A) (g (i+1):ℂ)
      Y.part (J₀).quiet=1 ∧ ∀ s:(J₀).Mode,s.val ⊆ active → s.val.card ≤ a → 
        ‖Y.part s-folded s‖ ≤ ε*(g b)^q ∧
        ‖(Order.value (g (i+1):ℂ) (Order.ratio W)).part s-folded s‖ ≤ (ε/2)*(g b)^q ∧
        ∀l,l ≤ order → Poly.toll L.w s*‖(Order.observe J₀ order (Order.logMarked W) l).part s-
          (K i ib x A l).part s‖ ≤ (((3:ℝ)⁻¹^(pow₀ a d q))/((order:ℝ)+1))*(g (i+1))^(pow₀ a d q)

variable (simple:G.Simple) (a d q shape span:ℕ) (U cap H angleCap ε:ℝ)
  (unit:1 ≤ U) (hp:0 ≤ angleCap) (ep:0<ε)
local notation "paid" => WilsonCoveredOrdinaryWindingPost.original R simple D φ grades order shelf k seats span
  (pow₀ a d q) H angleCap hp (ε:=(3:ℝ)⁻¹^(pow₀ a d q)) (by positivity)
local notation "closeFee" => WilsonReceivedCloseSourceCalendar.reporter_fee R simple
  (WilsonReceivedCloseOrdinaryGrade.nonneg J₀ a d q (zero_le_one.trans unit)) (half_pos ep)

def Ready (m₀:ℕ) : Prop :=
  (eventually_atTop.mp paid).choose ≤ m₀ ∧
  (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple shape cap)).choose ≤ m₀ ∧
  (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ m₀ ∧
  (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ m₀ ∧
  (eventually_atTop.mp closeFee).choose ≤ m₀

theorem scheduled : ∀ᶠ m₀:ℕ in atTop,
    Ready (k:=k) R D (φ:=φ) grades order shelf seats simple a d q shape span U cap H angleCap ε unit hp ep m₀ := by
  filter_upwards [eventually_ge_atTop (eventually_atTop.mp paid).choose,
    eventually_ge_atTop (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple shape cap)).choose,
    eventually_ge_atTop (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose,
    eventually_ge_atTop (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose,
    eventually_ge_atTop (eventually_atTop.mp closeFee).choose] with m₀ e f c p h
  exact ⟨e,f,c,p,h⟩

theorem original (start:P b mb source) (top:b<N) (K:Covered)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (law:VowsR.LawScroll G φ) (ch:VowsR.Chamber law R.kit D Q books)
    (volume:Volume.Fund D R.rolls Q φ books R.alloy.delay) (stage:k ≤ R.alloy.B.a.clock.J m)
    (cover:Match R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source start K)
    (active:Finset V) (rent:ℝ) (input:WilsonReceivedCloseOrdinaryRoster.Served R hk D Q π Γ Ψ books ahead
      actors pieces grades order shelf seats mb source start top span H angleCap active a (width U d) rent ((ε/2)*(g b)^q))
    (close:PaceR.Close R shape cap m b)
    (dates:Ready (k:=k) R D (φ:=φ) grades order shelf seats simple a d q shape span U cap H angleCap ε unit hp ep m) :
    Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source start top K span H angleCap active a d q U ε := by
  rcases dates with ⟨winds,bands,reverse,cools,delay⟩
  have cold := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec b
    (cools.trans mb) N per top.le
  have low:g b ≤ 1 := by linarith only [cold.1,cold.2]
  have fee:WilsonReceivedCloseOrdinaryGrade.invoice J₀ a d q U*g b ≤ ε/2 :=
    (eventually_atTop.mp closeFee).choose_spec b (delay.trans mb) N per top.le
  have cells:=(eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple shape cap)).choose_spec b
    (bands.trans mb) m mb close N per top.le
  intro i ib mi
  obtain ⟨L,walk,sold,heard⟩:=input i ib mi
  refine ⟨L,walk,sold,?_⟩
  intro x F tag A z B angle hz inside U₀ clear Y W folded
  obtain ⟨quiet,rows⟩:=heard x F tag A z hz inside clear
  refine ⟨quiet,?_⟩
  intro s hs ha
  have installed:=cover i mi ib L walk x A
  let C:=fun l=>Air.discharge (teacher i mi L x) l angle
  have named : WilsonCoveredOrdinaryPolynomial.evaluated order C (g (i+1):ℂ) s=folded s := by
    change WilsonCoveredOrdinaryPolynomial.evaluated order C _ s=WilsonCoveredOrdinaryPolynomial.evaluated order (K i ib x A) _ s
    apply congrArg (WilsonIndependentOrdinaryPairGrade.partialValue order (g (i+1):ℂ))
    unfold WilsonCoveredOrdinaryPolynomial.ordinary
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.prod_congr rfl
    intro t _
    unfold WilsonCoveredOrdinaryPolynomial.row
    exact Finset.sum_congr rfl (fun n hn=>congrArg (fun f:Poly J₀=>Polynomial.monomial n (f.part t.val))
      (installed n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).symm)
  have wind:=(eventually_atTop.mp paid).choose_spec i (winds.trans mi) hk (stage.trans (R.alloy.B.a.fits.mono mi))
    Q π Γ Ψ course books law ch volume mi (ib.trans_lt top) ahead actors pieces (read i ib) L x A
    z hz inside F tag
  have block:=wind.2 s (fun t ht=>(rows t.val (ht.trans hs) ((card_le_card ht).trans ha)).2.2)
  change Poly.toll L.w s * ‖(Order.value (g (i+1):ℂ) (Order.ratio W)).part s -
    WilsonCoveredOrdinaryPolynomial.evaluated order C (g (i+1):ℂ) s‖ ≤ _ at block
  rw [named] at block
  let value:=‖(Order.value (g (i+1):ℂ) (Order.ratio W)).part s-folded s‖
  have edge:=cells (i+1) (by omega) (by omega)
  have inv:=WilsonReceivedCloseOrdinaryScale.inverse R simple (per:=per) ib top (reverse.trans mb)
  have leakage:value ≤ (ε/2)*(g b)^q := WilsonCoveredOrdinaryRestored.paid s a d q U (g b) (g (i+1)) (ε/2)
    (Poly.toll L.w s) value unit cold.1 low edge.1 edge.2 inv (Poly.worth L.salary.positive s)
    (norm_nonneg _) ha (sold s hs) fee block
  refine ⟨?_,leakage,fun l hl=>?_⟩
  · have tr := dist_triangle (Y.part s) ((Order.value (g (i+1):ℂ) (Order.ratio W)).part s) (folded s)
    simp only [dist_eq_norm] at tr
    have left:‖Y.part s-(Order.value (g (i+1):ℂ) (Order.ratio W)).part s‖ ≤ (ε/2)*(g b)^q := (rows s hs ha).1
    change ‖(Order.value (g (i+1):ℂ) (Order.ratio W)).part s-folded s‖ ≤ _ at leakage
    linarith only [tr,left,leakage]
  · rw [installed l hl]
    exact wind.1 l hl s

end YM.Integration.WilsonReceivedCloseFoldedOrdinary

import YM.Integration.WilsonReceivedCloseFaceBudget
import YM.Integration.WilsonReceivedCloseEndpoint

/-! The complete-gallery output radius charged on its own original post at each capture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseGalleryWallet
open private currency from YM.Integration.WilsonReceivedCloseInterval
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open scoped BigOperators


open scoped Topology

/-- The actual spend is bounded by a stage forecast on every enrolled date before the reporter.
One spare coupling strip pays the entire forced-radius restoration at fixed active load. -/
theorem reserve {G:Gauge} (R:Run G) (simple:G.Simple) (a:ℕ) {η:ℝ} (ep:0<η) :
    ∀ᶠ m:ℕ in atTop, ∀ i b N per:ℕ, m ≤ i → i ≤ b → b ≤ N → ∀ Ω:ℝ, 0 ≤ Ω → Ω ≤ budgetR R i →
      Ω^(6*a) ≤ (regulatorRun R.family N per b)^(-η) := by
  let H := R.alloy.B.a.clock.hatBeta
  obtain ⟨start,paid⟩ := eventually_atTop.mp (WilsonMovingMentorPageReserve.powers R simple (6*a) (δ:=η/8) (by positivity))
  obtain ⟨first,high⟩ := eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)
  obtain ⟨last,hot⟩ := eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_ge_atTop start,eventually_ge_atTop first,eventually_ge_atTop last] with m h₀ h₁ h₂
  intro i b N per mi ib top Ω pos charged
  have warm := hot b (h₂.trans (mi.trans ib))
  have rise := WilsonStartup.Timing.hat_mono R.alloy.B.a (Gauge.slopeConstant_pos simple).le (Nat.succ_le_succ ib)
  have next := high b (h₁.trans (mi.trans ib))
  have room : H (i+1) ≤ (H b)^2 := by
    have quad : 2*H b ≤ (H b)^2 := by nlinarith only [warm,sq_nonneg (H b-2)]
    exact rise.trans (next.trans quad)
  have actual := (R.makes.wilson.represents N per b top).band.1
  have hp : 0 ≤ H (i+1) := zero_le_one.trans (R.alloy.B.a.fits.delayed _).le
  calc
    _ ≤ (H (i+1))^(η/8) := paid i (h₀.trans mi) Ω pos (charged.trans (min_le_right ..))
    _ ≤ ((H b)^2)^(η/8) := Real.rpow_le_rpow hp room (by positivity)
    _ = (H b)^(η/4) := by
      rw [←Real.rpow_natCast (H b) 2,←Real.rpow_mul (show 0 ≤ H b by linarith only [warm])]
      congr 1
      push_cast
      ring
    _ ≤ _ := currency warm actual ep

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




/-- Usable on the post already selected by the signed or ordinary comparison.
It retains the nominal radius of each group in the same physical gallery. -/
theorem original (P₀:P b mb source) (top:b ≤ N) (simple:G.Simple) {active:Finset V} {price:ℝ}
    (paid : WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats mb source P₀ active price)
    (a : ℕ) {η:ℝ} (ep : 0<η)
    (ready:(eventually_atTop.mp (reserve R simple (max 1 a) ep)).choose ≤ m)
    {i:ℕ} (ib:i ≤ b) (mi:m ≤ i) (L:P i mi (read i ib))
    (traced:WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ i mi (read i ib) L) :
    let Ω := Oak.expenseReal R hk D Q π Γ books mi L.op L.lesson ahead order shelf
    let w := Stoop.radius L.w (Ω^6)
    (∀ v∈active,(w v)⁻¹ ≤ (g b)^(-η)*price) ∧
      ∀ s : (Stock.census V).Mode, s.val⊆active → s.val.card ≤ a →
        (Poly.toll w s)⁻¹ ≤ (g b)^(-η)*price^s.val.card := by
  intro Ω w
  have quote := L.issued.Beamwork
  have one : 1 ≤ Ω := L.issued.Waffle.cool
  have base := (eventually_atTop.mp (reserve R simple (max 1 a) ep)).choose_spec m ready i b N per mi ib top
    Ω (zero_le_one.trans one) quote
  have seen := (paid i ib mi L traced).1
  have invoice (s:(Stock.census V).Mode) (names:s.val⊆active) (count:s.val.card ≤ max 1 a) :
      (Poly.toll w s)⁻¹ ≤ (g b)^(-η)*price^s.val.card := by
    have edges := (pow_le_pow_right₀ one (Nat.mul_le_mul_left 6 count)).trans base
    have sold := WilsonReceivedCloseFaceBudget.product L.salary.positive s names seen
    have amend : (Poly.toll w s)⁻¹=(Ω^(6*s.val.card))*(Poly.toll L.w s)⁻¹ := by
      simp only [w,Stoop.radius,Poly.toll,div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_const,mul_inv_rev,inv_pow,inv_inv,pow_mul]
    rw [amend]
    exact mul_le_mul edges sold (inv_nonneg.mpr (Poly.worth L.salary.positive _).le)
      (pow_nonneg (zero_le_one.trans one) _ |>.trans edges)
  refine ⟨?_,fun s hs hc=>invoice s hs (hc.trans (le_max_right ..))⟩
  intro v hv
  have stock := invoice ((Stock.census V).fire v) (by simpa only [Marker.Census.fire,Finset.singleton_subset_iff] using hv)
    (by simpa only [Marker.Census.fire,Finset.card_singleton] using (le_max_left 1 a))
  simpa only [Poly.toll,Marker.Census.fire,Finset.prod_singleton,Finset.card_singleton,pow_one] using stock

end YM.Integration.WilsonReceivedCloseGalleryWallet

import YM.Integration.WilsonReceivedCloseGalleryWallet
import YM.Integration.WilsonReceivedCloseChainFunding
namespace YM.Integration.WilsonCenteredCloseCaptureWallet
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

def width (r load : ℕ) := r*load+1

def price (U : ℝ) (r load : ℕ) := (1+U)^load*(3:ℝ)^width r load

private theorem charged {x y U : ℝ} (r j load : ℕ) (low : j ≤ load) (warm : 1 ≤ x)
    (nu : 0 ≤ U) (yn : 0 ≤ y) (same : y ≤ 3*x) :
    y*(U*y^r)^j ≤ price U r load*x^width r load := by
  have warm3 : 1 ≤ 3*x := by linarith
  have safe : 1 ≤ 1+U := by linarith
  have cmp : U*y^r ≤ (1+U)*(3*x)^r :=
    mul_le_mul (by linarith) (pow_le_pow_left₀ yn same _) (pow_nonneg yn _) (by linarith)
  have cmp1 : 1 ≤ (1+U)*(3*x)^r :=
    one_le_mul_of_one_le_of_one_le safe (one_le_pow₀ warm3)
  have caps := (pow_le_pow_left₀ (mul_nonneg nu (pow_nonneg yn _)) cmp j).trans
    (pow_le_pow_right₀ cmp1 low)
  calc
    _ ≤ (3*x)*((1+U)*(3*x)^r)^load :=
      mul_le_mul same caps (pow_nonneg (mul_nonneg nu (pow_nonneg yn _)) _) (by linarith)
    _ = _ := by simp only [price,width,pow_succ,pow_mul,mul_pow]; ring
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




/-- The reporter and every inherited face use the original close calendar and
the actual marked weights after the terminal six-radius restoration. -/
theorem original (P₀:P b mb source) (top:b ≤ N) (simple:G.Simple) {active:Finset V}
    (degree r load : ℕ) (occupied : 1 ≤ load) (budget U : ℝ) (nu : 0 ≤ U)
    (close : PaceR.Close R degree budget m b)
    (calendar : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree budget)).choose ≤ b)
    (ready : (eventually_atTop.mp (WilsonReceivedCloseGalleryWallet.reserve R simple (max 1 load)
      (show (0:ℝ) < 1 by norm_num))).choose ≤ m)
    (paid : WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats mb source P₀ active (U*((g b)⁻¹)^r))
    {i:ℕ} (ib:i ≤ b) (mi:m ≤ i) (cut:i < N) (L:P i mi (read i ib))
    (traced : WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ i mi (read i ib) L) (temp : 1 ≤ (g (i+1))⁻¹) :
    let Ω := Oak.expenseReal R hk D Q π Γ books mi L.op L.lesson ahead order shelf
    let w := Stoop.radius L.w (Ω^6)
    (∀v∈active,(w v)⁻¹ ≤ price U r load*((g (i+1))⁻¹)^width r load) ∧
    ∀s:(Stock.census V).Mode,s.val⊆active → s.val.card ≤ load → (Poly.toll w s)⁻¹ ≤ price U r load*((g (i+1))⁻¹)^width r load := by
  have cold: 0 < g b := ((eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree budget)).choose_spec
    b calendar m mb close N per top b mb top).1
  obtain ⟨live,bound⟩:=(eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree budget)).choose_spec
    b calendar m mb close N per top (i+1) (by omega) cut
  have same : (g b)⁻¹ ≤ 3*(g (i+1))⁻¹ := by
    rw [inv_eq_one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ cold live).mpr (by simpa only [one_mul] using bound)
  obtain ⟨one,all⟩ := WilsonReceivedCloseGalleryWallet.original R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats mb source P₀ top simple paid load (show (0:ℝ) < 1 by norm_num) ready ib mi L traced
  constructor
  · intro v hv
    have receipt:=one v hv
    simp only [Real.rpow_neg_one] at receipt
    have passage:=charged r 1 load occupied temp nu (inv_pos.mpr cold).le same
    rw [pow_one] at passage
    exact receipt.trans passage
  · intro s hs count
    have receipt:=all s hs count
    simp only [Real.rpow_neg_one] at receipt
    exact receipt.trans (charged r _ load count temp nu (inv_pos.mpr cold).le same)

end YM.Integration.WilsonCenteredCloseCaptureWallet

import YM.Integration.WilsonPhysicalExteriorFiniteLog
import YM.Integration.WilsonPhysicalExteriorRegulator

/-! Choosing the subtraction clock after the original moving finite regulator.
Finite geometry is tested in its own separated coordinates. Every fixed log
node is paid on one tent, one actual period and one archived bare amplitude. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorLogRegulator
open Function Set Filter MeasureTheory
open Lattice Precision RG PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Moving Epoch Calibration Rocket Oracle Circuit Lodge Ledger
open MS MS.Land MS.Menus MS.Rake MS.Dial MS.Logarithm
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles YM.FVAAlt2.Home Labels Source
open Extra.FD FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {X : Type}
variable (Y : Oracle.Program K) (Z : ∀ b : Patch,b.Branches K G) (C : Run G)
variable (R : Lodge.Contract C Y Z) (t : X → ℕ) (ht : ∀ i, R.floor Y Z C ≤ t i)
local notation "track" => WilsonPhysicalExteriorRegulator.nativeTrack Y Z C R t ht
variable (F : Calibration.Tent (R.profile Y Z C t ht).entire)
variable {B : MS.Local.Physical.Deck G} {O : Booked B} (H : MS_Data G O) (τ : Prescription B)
variable (ℓ : X → ℕ) (a : X → Cover) {n : ℕ} (D : Fin n → Label B) (k : ℕ)

private abbrev Input := ↥(conf n) × ℝ × ℝ × Sound.Formal.Episode (Fin n) C.family.labels

private def variation (u : ℝ) (z : Input (n:=n) C) :=
  PowerSeries.coeff k (Sound.Formal.dated τ (u-z.2.1) (Lodge.basisR C) D z.2.2.1 z.2.2.2) -
    Dial.tour H D u (Home.Profiles.realize z.1.val) Finset.univ k

private theorem law : Ready (variation C H τ D k) := by
  have hF := WilsonPhysicalExteriorFiniteLog.dated τ (Lodge.basisR C) D
    (fun z : Input (n:=n) C => z.2.1) (fun z => z.2.2.1) (fun z => z.2.2.2) k
  have hH := MSExteriorFiniteScales.tour_polynomial H D
    (fun z : Input (n:=n) C => Home.Profiles.realize z.1.val)
    (fun z => Home.Profiles.realize_one z.1.property) k
  exact hF.sub hH

/-- One finite set of subtraction clocks and one polynomial bound are chosen
before any mesh coordinates, terminal phases, available periods or requested log. -/
theorem nodes :
    ∃ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∃ b : ℕ, ∀ i (q : Pegs.Motor track n i),
      CalendarT.sample i q ∈ conf n → ∀ v U : ℝ, 0 ≤ U →
      (∀ j ∈ Finset.range m, Pegs.Error Y Z C R t ht F D τ H (j:ℝ) ℓ a k i q ≤ U) →
      Pegs.Error Y Z C R t ht F D τ H v ℓ a k i q ≤ A*(1+|v|)^b*U := by
  obtain ⟨m,A,hA,b,hu⟩ := MSExteriorFiniteScales.finite_observations (law C H τ D k)
  refine ⟨m,A,hA,b,?_⟩
  intro i q hq v U hU hj
  let z : Input (n:=n) C := (⟨CalendarT.sample i q,hq⟩,(track).Θ i,Sound.Alone track i,
    Sound.Figure.perRead C Z (Period.Field.LodgeT.instance_real Y Z C R t ht)
      (fun _ j => a i+Lattice.lift (q j)) (Calibration.sheet F) (ℓ i) ((track).stop.choose i))
  have raw (u : ℝ) : Pegs.Error (u:=B) (J:=O) Y Z C R t ht F D τ H u ℓ a k i q =
      ‖variation C H τ D k u z‖ := rfl
  rw [raw v]
  exact hu z v U hU (fun j hm => (raw j) ▸ hj j hm)

variable (l : Filter X) (N : ℕ) (htop : Tendsto t l atTop)

include htop in
/-- The actual original soft closure rate can be posted once for all integer
subtraction nodes. Any cofinally larger period remains available for the same book. -/
theorem periods :
    ∃ L : X → ℕ, ∀ ℓ' : X → ℕ, (∀ᶠ i in l,L i ≤ ℓ' i) → ∀ j : ℕ,
      Study.Holding Y Z C R t ht F N τ (j:ℝ) ℓ' l := by
  choose κ hk using fun j : ℕ => Study.hold_all Y Z C R t ht F N τ (j:ℝ) l htop
  let L := fun i => ∑ j ∈ Finset.range (t i),κ j i
  refine ⟨L,fun ℓ' hℓ j => hk j ℓ' ?_⟩
  filter_upwards [hℓ,htop.eventually (eventually_gt_atTop j)] with i hi hj
  exact (Finset.single_le_sum (f:=fun q => κ q i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hj)).trans hi

variable {g : G.ColorIndex}
variable (notebook : Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F N)
variable (venue : (R.profile Y Z C t ht).VenueT a) (hN : ∀ i, N≤t i) (hG : G.Simple)
variable (fit : MS.Land.TaylorOKPl H (Lobby.Table (Lodge.basisR C) B) τ)
variable (hℓ : ∀ j : ℕ, Study.Holding Y Z C R t ht F N τ (j:ℝ) ℓ l)
variable (E : Set (Points n)) (hE : IsCompact E) (he : E ⊆ conf n)

include hG htop notebook venue hN fit hℓ hE he in
/-- The quantitative gap is earned on the true signed periodic coefficient, at
all requested log clocks at once, not just one comparison with a fixed MS scale. -/
theorem pixels (hk : k ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ d : ℕ, ∀ᶠ i in l, ∀ q : Pegs.Motor track n i,
      CalendarT.sample i q ∈ E → ∀ v : ℝ,
      Pegs.Error Y Z C R t ht F D τ H v ℓ a k i q ≤ A*(1+|v|)^d*Sound.BudgetAir track i := by
  let cap := ∑ j, (D j).h
  have fixed (j : ℕ) : ∃ K₀ : ℝ, 0<K₀ ∧ ∀ᶠ i in l, ∀ q : Pegs.Motor track n i,
      CalendarT.sample i q ∈ E → Pegs.Error Y Z C R t ht F D τ H (j:ℝ) ℓ a k i q ≤
        K₀*Sound.BudgetAir track i := by
    obtain ⟨σ,hσ,hσℓ⟩ := hℓ j n cap
    exact Pegs.uniform hG Y Z C R t ht F N cap D τ H (j:ℝ) ℓ a hE he l htop notebook venue hN fit
      hσ hσℓ (fun j => Finset.single_le_sum (f:=fun j => (D j).h) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)) k hk
  obtain ⟨m,A,hA,b,hb⟩ := nodes Y Z C R t ht F H τ ℓ a D k
  choose c hc hcut using fixed
  let C₀ := ∑ j ∈ Finset.range m,c j
  have hC : 0 ≤ C₀ := Finset.sum_nonneg fun j _ => (hc j).le
  refine ⟨A*C₀,mul_nonneg hA hC,b,?_⟩
  have joined := (Finset.range m).eventually_all.mpr (fun j _ => hcut j)
  filter_upwards [joined] with i hi
  intro q hq v
  have hβ : 0≤Sound.BudgetAir track i := (Real.exp_pos _).le
  have H₀ := hb i q (he hq) v (C₀*Sound.BudgetAir track i) (mul_nonneg hC hβ) (fun j hj =>
    (hi j hj q hq).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f:=c) (fun j _ => (hc j).le) hj) hβ))
  exact H₀.trans_eq (by ring)

end YM.Integration.WilsonPhysicalExteriorLogRegulator

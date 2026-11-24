import YM.Integration.WilsonOriginalOpticalSpot
import YM.WilsonCoeffUV.Product.Report.Pre

/-! Pre-length and post-length prices on the actual marked tokenizer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOpticalTariffs
open Function Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonLimitConstruction
open PowerSeries Blue Mer Embroider Embroider.Canvas Soil Laurent Cosmos Gauge Power Matrix Tree Exterior
open AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Polestar Supply Ticket Flooring
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
open Finset
variable {G : Gauge}

/-- One pre-block number at two specific stages, independent of the length,
cutoffs, period, or actual marked rows. -/
def factor (G : Gauge) (K : KernelChoices) (i j u : ℕ) (h : 4 ≤ i ∧ 5 ≤ j) : ℝ :=
  let t := raySmall G K i j h.1 h.2
  t.preB * tender (Hooks G) t.s u

theorem factor_nn (G : Gauge) (K : KernelChoices) (i j u : ℕ) (h : 4 ≤ i ∧ 5 ≤ j) :
    0 ≤ factor G K i j u h :=
  mul_nonneg (raySmall G K i j h.1 h.2).pre_nn
    (tender_nn (raySmall G K i j h.1 h.2).sigma ..)

def floor (G : Gauge) (K : KernelChoices) (i j u r : ℕ) : ℕ :=
  if good : (4 ≤ i ∧ 5 ≤ j) ∧ 0 < r then
    (eventually_atTop.mp (leave good.2 (factor G K i j u good.1) (factor_nn ..) u)).choose
  else 0

/-- A stage bounds all retained ranks up to 2j and every request u up to j. -/
def before (G : Gauge) (K : KernelChoices) (j : ℕ) : ℕ :=
  (univ : Finset (Fin (j+1) × Fin (j+1) × Fin (2*j+1))).sup
    (fun s => floor G K s.1 j s.2.1 s.2.2)

theorem pin {A : Levels G} {Ñ : ChartRatio G} {m k e u : ℕ} (w : Usage A Ñ m)
    (live : 5 ≤ A.clock.J (m+1))
    (length : before G A.clock.kernel (A.clock.J (m+1)) ≤ (A.S.block m).val)
    (fit : max k (max e u) ≤ A.clock.J (m+1))
    (shape : w.s = (raySmall G A.clock.kernel _ _ (A.clock.adm m) live).s)
    (pre : w.preB = (raySmall G A.clock.kernel _ _ (A.clock.adm m) live).preB) :
    prevec G w.gear k e u := by
  intro r pos retained
  let i := A.clock.J m
  let j := A.clock.J (m+1)
  have ih : i ≤ j := A.fits.mono m.le_succ
  have uh : u ≤ j := ((le_max_right ..).trans (le_max_right ..)).trans fit
  have kh : k ≤ j := (le_max_left ..).trans fit
  have eh : e ≤ j := ((le_max_left ..).trans (le_max_right ..)).trans fit
  have rh : r ≤ 2*j := by omega
  let tr : Fin (j+1) × Fin (j+1) × Fin (2*j+1) :=
    (⟨i,Nat.lt_succ_of_le ih⟩,⟨u,Nat.lt_succ_of_le uh⟩,⟨r,Nat.lt_succ_of_le rh⟩)
  have threshold : floor G A.clock.kernel i j u r ≤ (A.S.block m).val :=
    (Finset.le_sup (f:=fun s : Fin (j+1) × Fin (j+1) × Fin (2*j+1) =>
      floor G A.clock.kernel s.1 j s.2.1 s.2.2) (mem_univ tr)).trans length
  have legal : (4 ≤ i ∧ 5 ≤ j) ∧ 0 < r := ⟨⟨A.clock.adm m,live⟩,pos⟩
  rw [floor, dif_pos legal] at threshold
  have result := (eventually_atTop.mp
    (leave pos (factor G A.clock.kernel i j u legal.1) (factor_nn ..) u)).choose_spec _ threshold
  rw [pinCost,if_neg pos.ne']
  change (w.preB / (A.S.block m).val * tender (Hooks G) w.s u)^r * 9^u ≤ _
  rw [pre,shape,div_mul_eq_mul_div]
  exact result

def row (I : Gear G) (k e u : ℕ) : ℝ := (eventually_atTop.mp (PostHive I k e u 0)).choose

/-- All remaining DormP costs can see the realized gear after the length. -/
def after (j : ℕ) (I : Gear G) : ℝ :=
  ∑ x : Fin (j+1) × Fin (j+1) × Fin (j+1), |row I x.1 x.2.1 x.2.2|

theorem spent (I : Gear G) (k e u j : ℕ) (c : ℝ)
    (fit : max k (max e u) ≤ j) (bill : after j I ≤ c) (openPins : prevec G I k e u) :
    DormP I k e u c := by
  have kh : k ≤ j := (le_max_left ..).trans fit
  have eh : e ≤ j := ((le_max_left ..).trans (le_max_right ..)).trans fit
  have uh : u ≤ j := ((le_max_right ..).trans (le_max_right ..)).trans fit
  let tr : Fin (j+1) × Fin (j+1) × Fin (j+1) :=
    (⟨k,Nat.lt_succ_of_le kh⟩,⟨e,Nat.lt_succ_of_le eh⟩,⟨u,Nat.lt_succ_of_le uh⟩)
  have price : row I k e u ≤ c := (le_abs_self _).trans
    ((Finset.single_le_sum (f:=fun x : Fin (j+1) × Fin (j+1) × Fin (j+1) =>
      |row I x.1 x.2.1 x.2.2|) (fun _ _ => abs_nonneg _) (mem_univ tr)).trans bill)
  exact ((eventually_atTop.mp (PostHive I k e u 0)).choose_spec c price openPins).1

theorem gain {A : Levels G} {Ñ : ChartRatio G} {m : ℕ} (w : Usage A Ñ m)
    (live : 5 ≤ A.clock.J (m+1)) (stamp : w.σ = crestM A m live)
    (shape : w.s = (raySmall G A.clock.kernel _ _ (A.clock.adm m) live).s) :
    w.gear.s = 2*w.σ ∧ 3*w.σ ≤ 2*elixir w.gear := by
  have same : w.s = 2 * w.σ := by
    rw [shape,stamp]
    change saffron G _ _ _ _ _ = 2*(saffron G _ _ _ _ _ / 2)
    ring
  refine ⟨same,?_⟩
  change 3*w.σ ≤ 2*((w.s+w.σ)/2)
  linarith

end YM.Integration.WilsonOriginalOpticalTariffs
end

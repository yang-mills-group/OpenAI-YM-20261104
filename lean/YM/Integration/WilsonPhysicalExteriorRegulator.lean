import YM.Integration.WilsonPhysicalExteriorFormalPrice
import YM.Integration.NativeFVAPlateauCorrelation

/-! The signed far-coordinate correction on the actual moving formal Wilson regulator.
The finite side is its original periodized coefficient with its purchased field
fees and coupling change. The continuum side uses the identical sampled placement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRegulator
open Function Set Filter MeasureTheory Matrix
open Lattice Precision RG PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT
open MS MS.Land MS.Menus MS.Rake MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles YM.FVAAlt2.Home
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open FVA2 FVA2.ColorCode OPE.Levy Extra.FD
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {X : Type}
abbrev runDeck (C : Run G) : MS.Local.Physical.Deck G :=
  Home.seats (Study.Plan C).liftOff (Study.Plan C).certified
variable (Y : Oracle.Program K) (Z : ∀ b : Patch,b.Branches K G) (C : Run G)
variable (R : Lodge.Contract C Y Z) (t : X → ℕ) (ht : ∀ i, R.floor Y Z C ≤ t i)
abbrev nativeTrack : Lodge.Track X := R.profile Y Z C t ht
local notation "track" => nativeTrack Y Z C R t ht
local notation "B" => runDeck C
variable {O : Booked (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified)} (H : MS_Data G O)
variable (τ : Prescription (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified))
variable (F : Calibration.Tent (R.profile Y Z C t ht).entire) (ℓ : X → ℕ) (x : X → Cover) (μ : ℝ)
variable {n : ℕ} (v : Fin n → Label (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified)) (h : ℕ)
local notation "I" => Glyph B h

/-- All inner slots keep their prescribed labels; the exterior probing slot spans
the entire original glyph alphabet of the specified positive or zero horizon. -/
def marked {B' : MS.Local.Physical.Deck G} (u : Fin n → Label B') (cap : ℕ)
    (b : Glyph B' cap) : Fin (n+1) → Label B' :=
  Fin.append u (fun _ : Fin 1 => FVA2.ColorCode.labelAt B' b)

def finite (i : X) (q : Pegs.Motor (R.profile Y Z C t ht) (n+1) i) (b : I) : PowerSeries ℂ :=
  Pegs.grain (G:=G) (K:=K) (X:=X) (u:=runDeck C) (n:=n+1) Y Z C R t ht F (marked v h b) τ μ ℓ x i q

def sampled (i : X) (q : Pegs.Motor (R.profile Y Z C t ht) (n+1) i) (b : I) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => Dial.tour H (marked v h b) μ
    (Home.Profiles.realize (CalendarT.sample (T:=R.profile Y Z C t ht) i q)) Finset.univ k)

variable {l : Filter X} {N : ℕ} {g : G.ColorIndex}
variable {W : ∀ j : ℕ, Matrix (RG10.Position.Deck C.family.labels j)
  (RG10.Position.Deck C.family.labels j) (PowerSeries ℝ)}
variable (paid : Supplier.Funding (G:=G) (K:=K) (X:=X) (J':=O) Y Z C R t ht l τ W N g H μ F)
variable (walk : Supplier.Walk (G:=G) (K:=K) (X:=X) Y Z C R t ht μ τ N l x F ℓ)
variable (E : Set (Points (n+1))) (hE : IsCompact E) (hs : E ⊆ conf (n+1))

include paid walk hE hs in
/-- A single original cutoff gate for every outer glyph and coupling coefficient.
The fee is still the original mesh gain, before the chosen far readout. -/
theorem rows :
    ∃ A : ℝ, 0≤A ∧ ∀ᶠ i in l, ∀ (q : Pegs.Motor track (n+1) i),
      CalendarT.sample i q ∈ E → ∀ k ≤ N,
      ‖fun b : I => PowerSeries.coeff k (finite Y Z C R t ht τ F ℓ x μ v h i q b) -
        PowerSeries.coeff k (sampled Y Z C R t ht H μ v h i q b)‖ ≤
          A * Sound.BudgetAir track i := by
  choose c hc hp using fun z : I × Fin (N+1) =>
    paid.points x ℓ walk (n+1) E hE hs (marked v h z.1) z.2.val (Nat.le_of_lt_succ z.2.isLt)
  let A : ℝ := ∑ z, c z
  have hA : 0≤A := Finset.sum_nonneg fun j _ => (hc j).le
  have he : ∀ᶠ i in l,∀ z, ∀ q : Pegs.Motor track (n+1) i, CalendarT.sample i q ∈ E →
      Pegs.Error Y Z C R t ht F (marked v h z.1) τ H μ ℓ x z.2.val i q ≤
        c z * Sound.BudgetAir track i := Filter.eventually_all.mpr hp
  refine ⟨A,hA,?_⟩
  filter_upwards [he] with i hi
  intro q hq k hk
  have hβ : 0≤Sound.BudgetAir track i := (Real.exp_pos _).le
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA hβ)).mpr
  intro b
  let z : I × Fin (N+1) := (b, ⟨k,Nat.lt_succ_of_le hk⟩)
  have hz : c z ≤ A :=
    Finset.single_le_sum (f:=c) (fun j _ => (hc j).le) (Finset.mem_univ z)
  simpa only [z,Pegs.Error,finite,sampled,PowerSeries.coeff_mk] using
    (hi z q hq).trans (mul_le_mul_of_nonneg_right hz hβ)

variable (V : Warehouse G) (p₀ p₁ : E4) (hp : p₀ ≠ p₁)

/-- The coefficient of the actual full signed far row times its formal inverse.
The two factors carry their own order in the coupling. -/
def readout (T : ℝ) (k : ℕ) (y : I → PowerSeries ℂ) : I → ℂ :=
  ∑ j ∈ Finset.range (k+1),
    (PowerSeries.coeff j (WilsonPhysicalExteriorFormalGram.decoder V H h p₀ p₁ hp μ
      (Real.log T))).vecMul (fun b => PowerSeries.coeff (k-j) (y b))

include paid walk hE hs in
/-- With the original finite cutoff, period, and independent MS table kept fixed
in each pair of measurements, the decoder multiplies the native mesh error by
at most its sharp engineering power times a polynomial in the relative log. -/
theorem charged :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∃ d : ℕ, ∀ᶠ i in l, ∀ (q : Pegs.Motor track (n+1) i),
      CalendarT.sample i q ∈ E → ∀ T : ℝ, 1 ≤ T → ∀ k ≤ N,
      ‖readout C H μ h V p₀ p₁ hp T k (finite Y Z C R t ht τ F ℓ x μ v h i q) -
       readout C H μ h V p₀ p₁ hp T k (sampled Y Z C R t ht H μ v h i q)‖ ≤
        K₀*T^h*(1+Real.log T)^d*Sound.BudgetAir track i := by
  obtain ⟨A,hA,hrows⟩ := rows Y Z C R t ht H τ F ℓ x μ v h paid walk E hE hs
  obtain ⟨K₁,hK,d,hinv⟩ := WilsonPhysicalExteriorFormalPrice.readout V H h p₀ p₁ hp μ N
  refine ⟨((N+1:ℕ):ℝ)*K₁*A,by positivity,d,?_⟩
  filter_upwards [hrows] with i hi
  intro q hq T hT k hk
  have hL := Real.log_nonneg hT
  have hT₀ := zero_le_one.trans hT
  have hβ : 0≤Sound.BudgetAir track i := (Real.exp_pos _).le
  let y := finite Y Z C R t ht τ F ℓ x μ v h i q
  let z := sampled Y Z C R t ht H μ v h i q
  let errRow (j : ℕ) : I → ℂ := fun b => PowerSeries.coeff j (y b)-PowerSeries.coeff j (z b)
  let D := WilsonPhysicalExteriorFormalGram.decoder V H h p₀ p₁ hp μ (Real.log T)
  let fee := K₁*T^h*(1+Real.log T)^d
  have hfee : 0≤fee := by dsimp [fee]; positivity
  have width (j : ℕ) (hj : j ∈ Finset.range (k+1)) :
      ‖(PowerSeries.coeff j D).vecMul (errRow (k-j))‖ ≤ fee*(A*Sound.BudgetAir track i) := by
    have hjk := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact (hinv T hT j (hjk.trans hk) _).trans
      (mul_le_mul_of_nonneg_left (hi q hq _ ((Nat.sub_le k j).trans hk)) hfee)
  have he : readout C H μ h V p₀ p₁ hp T k y - readout C H μ h V p₀ p₁ hp T k z =
      ∑ j ∈ Finset.range (k+1), (PowerSeries.coeff j D).vecMul (errRow (k-j)) := by
    unfold readout
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Matrix.sub_vecMul _ _ _).symm
  change ‖readout C H μ h V p₀ p₁ hp T k y - readout C H μ h V p₀ p₁ hp T k z‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), ‖(PowerSeries.coeff j D).vecMul (errRow (k-j))‖ := norm_sum_le ..
    _ ≤ ∑ _j ∈ Finset.range (k+1), fee*(A*Sound.BudgetAir track i) := Finset.sum_le_sum width
    _ = ((k+1:ℕ):ℝ)*(fee*(A*Sound.BudgetAir track i)) := by simp
    _ ≤ ((N+1:ℕ):ℝ)*(fee*(A*Sound.BudgetAir track i)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hk) (by positivity)
    _ = _ := by dsimp [fee]; ring

end YM.Integration.WilsonPhysicalExteriorRegulator

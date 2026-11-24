import YM.Integration.WilsonLimitConstruction.FundedPointMarkedSeed
import YM.Integration.OriginalFrozenSourceInvoice
import YM.Integration.WilsonStartupClock
import YM.Integration.ActualRunAdjacentHatBeta

/-! The genuine shifted point coefficients have a fixed polynomial cost before
periods, source locations, completed regulators and tests. A finite number of
adjacent transports changes only its constant. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPointSourceClock
open Function Finset Filter Lattice RG Wilson Source Marker PhysicalNext.Repeat.Legato
open ComparisonDensity.Address RG05Readout RG05Readout.Native RG05Readout.Flatten
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet OriginalSourceJetAddresses IndependentSourcePathFamily
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Run G)
    {B : MS.Local.Physical.Deck G} (P : MS.Land.Prescription B)
    (grades weights : V→ℕ) (labs : V→MS.Rake.Label B) (μ : ℝ)
    (k : V→ℕ) (e : ℕ) (normal : V→ℂ) (quadrature : V→Bool)

local notation "reference" => FundedPointMarkedSeed.reference R grades weights

theorem polynomial (budget : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ d : ℕ,∀ N (orders : V→ℕ), (∀i,orders i≤budget) →
      bill (FundedPointMarkedSeed.source R P grades weights labs (μ-R.family.S.scale N)
        orders normal quadrature) k e 4 ≤ C*(1+‖R.family.S.scale N‖)^d := by
  let W := OriginalFrozenSourceInvoice.weight (reference) labs k e 4 normal
  have fw (i) : 0<W i := by
    apply add_pos_of_pos_of_nonneg zero_lt_one
    apply Finset.sum_nonneg
    intro s _
    apply mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _))
    exact Finset.sum_nonneg (fun _ _=>flour_nn ..)
  obtain ⟨C,_,d,cost⟩ := ActualOriginalQCharges.packet_cost_clock_bound
    (reference) labs P μ budget W 4 fw
  let T := ActualOriginalQCharges.totalRowPrice (reference) labs W 4
  refine ⟨max 1 (C*T),zero_lt_one.trans_le (le_max_left _ _),d,?_⟩
  intro N orders cap
  have invoice := OriginalFrozenSourceInvoice.input P (reference) labs (μ-R.family.S.scale N)
    orders k N e 4 normal quadrature (Nat.zero_le _)
  calc _ ≤ ActualOriginalQPackets.packetCost P (reference) labs (μ-R.family.S.scale N) orders N W 4 := invoice
       _ ≤ (C*(1+‖R.family.S.scale N‖)^d)*T := cost N (Nat.zero_le _) orders cap
       _ = (C*T)*(1+‖R.family.S.scale N‖)^d := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by positivity) _)

theorem clock (hG : G.Simple) (h : ℕ) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ m in atTop,∀ t : ℕ,t≤h →
      1+‖R.family.S.scale (m+1+t)‖ ≤ D*R.family.path.levels.clock.hatBeta m := by
  let L := R.family.path.levels
  obtain ⟨a,ha,growth⟩ := WilsonStartupClock.growth R hG
  obtain ⟨b,hb⟩ := eventually_atTop.mp growth
  obtain ⟨c,hc⟩ := eventually_atTop.mp (ActualRunAdjacentHatBeta.three_halves R hG)
  refine ⟨a*2^h,mul_pos ha (pow_pos (by norm_num) _),?_⟩
  filter_upwards [eventually_ge_atTop b,eventually_ge_atTop c] with m first step
  have climb (t : ℕ) : L.clock.hatBeta (m+t)≤(2:ℝ)^t*L.clock.hatBeta m := by
    induction t with
    | zero => simp
    | succ t ih =>
      have bound : L.clock.hatBeta (m+t+1) ≤ (3/2:ℝ)*L.clock.hatBeta (m+t) :=
        hc (m+t) (by omega)
      have pos : 0≤L.clock.hatBeta (m+t) := (zero_lt_one.trans (L.fits.delayed _)).le
      calc _≤(2:ℝ)*L.clock.hatBeta (m+t) := by
              change L.clock.hatBeta (m+t+1) ≤ _
              exact bound.trans (mul_le_mul_of_nonneg_right (by norm_num : (3/2:ℝ)≤2) pos)
           _≤2*((2:ℝ)^t*L.clock.hatBeta m) := mul_le_mul_of_nonneg_left ih (by norm_num)
           _=(2:ℝ)^(t+1)*L.clock.hatBeta m := by rw [pow_succ];ring
  intro t lev
  have upper := hb (m+t) (by omega)
  rw [show m+t+1=m+1+t by omega] at upper
  calc _≤a*L.clock.hatBeta (m+t) := upper
       _≤a*((2:ℝ)^t*L.clock.hatBeta m) := mul_le_mul_of_nonneg_left (climb t) ha.le
       _≤a*((2:ℝ)^h*L.clock.hatBeta m) := mul_le_mul_of_nonneg_left
         (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) lev)
           (zero_lt_one.trans (L.fits.delayed _)).le) ha.le
       _=(a*2^h)*L.clock.hatBeta m := (mul_assoc ..).symm

theorem window (hG : G.Simple) (h budget : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ d : ℕ,∀ᶠ m in atTop,∀ (t : ℕ), t≤h →
      ∀ (per b : ℕ) (o : V→Site (R.family.side b per)) (orders : V→ℕ), (∀i,orders i≤budget) →
        bill (FundedOriginalMarkedInput.chosen P (FundedPointMarkedSeed.datum R grades weights per b o)
          labs (μ-R.family.S.scale (m+1+t)) orders normal quadrature) k e 4 ≤
          C*(R.family.path.levels.clock.hatBeta m)^d := by
  obtain ⟨C,hC,d,raw⟩ := polynomial R P grades weights labs μ k e normal quadrature budget
  obtain ⟨D,hD,near⟩ := clock R hG h
  refine ⟨C*D^d,mul_pos hC (pow_pos hD _),d,?_⟩
  filter_upwards [near] with m dates t ht per b o orders cap
  rw [FundedPointMarkedSeed.invoice R P grades weights labs (μ-R.family.S.scale (m+1+t)) orders normal quadrature]
  calc _≤C*(1+‖R.family.S.scale (m+1+t)‖)^d := raw _ orders cap
       _≤C*(D*R.family.path.levels.clock.hatBeta m)^d := mul_le_mul_of_nonneg_left
         (pow_le_pow_left₀ (by positivity) (dates t ht) d) hC.le
       _=(C*D^d)*R.family.path.levels.clock.hatBeta m^d := by rw [mul_pow];ring

end YM.Integration.WilsonLimitConstruction.FundedPointSourceClock
end

import YM.Integration.WilsonRootedOPEOilTariff
import YM.Integration.WilsonRootedOPEPointRows

/-! The full original normalizer that restores a raw point OPE is polynomial in
the actual cutoff calendar, uniformly in the request, period and all point placements. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPointNormalizer
open Function Finset Lattice Wilson RG Marker Source Labels
open PhysicalNext.Repeat.Legato LocalComparison ActualOriginalQReaders ActualOriginalQPackets ActualOriginalQCharges
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped BigOperators Classical
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G} (R:Run G) (simple:G.Simple)
variable (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B) (μ:ℝ) (orders:V→ℕ)
local notation "β" => R.family.path.levels.clock.hatBeta

def polynomial (s:Slot u) : Polynomial ℝ := ((Q.fees (u s.1).h (u s.1).item) (orders s.1)).register s.2

def degree : ℕ := ∑z:Row (R:=R) u,(polynomial Q u orders z.1).natDegree

include simple in
theorem purchased : ∃ C:ℝ,0<C ∧ ∀(J:Request V) (A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V)) (o:V→Site (R.family.side (d.level+1) d.period)),
    ActualOriginalQInitialInput.normalizer R simple u J A d Q o μ orders ≤ C*β d.cutoff^(degree R Q u orders) := by
  classical
  let K:=degree R Q u orders
  let cr (z:Row (R:=R) u):=WilsonRootedOPEPointRows.tariff R u z
  have buys (z:Row (R:=R) u) := WilsonRootedOPEOilTariff.polynomial R simple μ (polynomial Q u orders z.1)
  choose c nc all using buys
  let C:=max 1 (∑z:Row (R:=R) u,c z*cr z)
  have C1:1 ≤ C := le_max_left _ _
  refine ⟨C,zero_lt_one.trans_le C1,?_⟩
  intro J A d o
  let N:=d.cutoff
  let D:=ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
  let width:=(ActualOriginalQInitialInput.schedule R simple u J A).inputWidth d.level
  have clipped:width ≤ 1 := ActualBoundedNumericSchedule.input_width_le_one R simple (ActualOriginalQPointSetup.schedule R u J A) d.level
  have β1:= (R.family.path.levels.fits.delayed N).le
  have item (z:Row (R:=R) u) : ‖fee Q u (μ-R.family.S.scale N) orders z.1‖ * rowPrice D u (fun _=>1) width z ≤ (c z*cr z)*β N^K := by
    have deg:(polynomial Q u orders z.1).natDegree ≤ K :=
      Finset.single_le_sum (f:=fun j:Row (R:=R) u=>(polynomial Q u orders j.1).natDegree) (fun _ _=>Nat.zero_le _) (mem_univ z)
    have pol : ‖fee Q u (μ-R.family.S.scale N) orders z.1‖ ≤ c z*β N^K := by
      change ‖(((polynomial Q u orders z.1).eval (μ-R.family.S.scale N):ℝ):ℂ)‖ ≤ _
      rw [Complex.norm_real,Real.norm_eq_abs]
      exact (all z N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ β1 deg) (nc z))
    calc
      _ ≤ ‖fee Q u (μ-R.family.S.scale N) orders z.1‖*cr z :=
        mul_le_mul_of_nonneg_left (WilsonRootedOPEPointRows.bounded R u J o clipped z) (norm_nonneg _)
      _ ≤ (c z*β N^K)*cr z := mul_le_mul_of_nonneg_right pol (WilsonRootedOPEPointRows.nonneg R u z)
      _ = _ := by ring
  change max 1 (∑z:Row (R:=R) u,‖fee Q u (μ-R.family.S.scale N) orders z.1‖ * rowPrice D u (fun _=>1) width z) ≤ C*β N^K
  apply max_le
  · exact C1.trans (le_mul_of_one_le_right (zero_le_one.trans C1) (one_le_pow₀ β1))
  · calc
      _ ≤ ∑z:Row (R:=R) u,(c z*cr z)*β N^K := sum_le_sum fun z _=>item z
      _ = (∑z:Row (R:=R) u,c z*cr z)*β N^K := (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans β1) _)

end YM.Integration.WilsonRootedOPEPointNormalizer

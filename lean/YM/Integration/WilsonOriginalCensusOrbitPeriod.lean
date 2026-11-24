import YM.Integration.WilsonOriginalCensusFiniteWinding
import YM.Integration.WilsonMarkedIndependentMixedOrderedWinding

/-! Both physical finite-board windings and the relative orbit aperture
vanish on a single opening chosen before the physical ultraviolet cutoff,
including on every further auxiliary multiple of the physical period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusOrbitPeriod
open Work.F08 WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Cadenza
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonReceivedDatedVerseReprint WilsonReceivedCompactVerseEntrance
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators

open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained)
open WilsonPointChildRelativeLift (centers)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonCoeffUV.Bank.Carp (plume)


open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open WilsonOriginalCensusOrbitCenters (layout shifted)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)
open scoped Classical BigOperators
variable {G:Gauge}{e v:ℕ}{D k:Fin v→ℕ}{I:Type}[Fintype I][DecidableEq I]{H:I→ℕ}


open Filter WilsonCoeffUV.Winding
open scoped Topology

theorem below {κ:ℝ}(hκ:0≤κ){n X:Side}(h:n.val∣X.val):catchW κ X ≤ catchW κ n:=by
  have small:(n.val:ℝ) ≤ X.val:=by exact_mod_cast Nat.le_of_dvd X.pos h
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left small (neg_nonpos.mpr hκ))

theorem cost (R:Run G)(m d:ℕ)(s t A B C ε:ℝ)(hs:0<s)(ht:0<t)(he:0<ε):
    ∀ᶠ per:ℕ in atTop,∀n X:Side,(R.family.side m per).val∣n.val → n.val∣X.val →
    32*d<n.val ∧ Real.exp (-(((s/2)/2)*((n.val:ℝ)-d))/2)*A+
      B*catchW (s/512) X+C*catchW (t/512) n ≤ ε:=by
  have grow:Tendsto (fun p:ℕ=>(R.family.side m p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(R.family.side m p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator m).pos).tendsto_atTop
  have small (a u:ℝ)(hu:0<u):Tendsto (fun p:ℕ=>a*catchW u (R.family.side m p)) atTop (𝓝 0):=by
    simpa only [mul_zero] using (WilsonMarkedIndependentMixedOrderedWinding.disappears
      (b:=m) R u hu).const_mul a
  let A':=Real.exp (s*(d:ℝ)/8)*A
  have h1:=small |A'| (s/8) (by positivity)
  have h2:=small |B| (s/512) (by positivity)
  have h3:=small |C| (t/512) (by positivity)
  have all:=((h1.add h2).add h3).eventually_lt_const (show (0:ℝ)+0+0<ε by simpa using he)
  filter_upwards [tendsto_atTop.1 grow (32*d+1),all] with per ample budget
  intro n X size more
  refine ⟨lt_of_lt_of_le ample (Nat.le_of_dvd n.pos size),?_⟩
  have magnitude (a u:ℝ)(hu:0≤u)(T:Side)(leaves:(R.family.side m per).val∣T.val):
      a*catchW u T≤|a| * catchW u (R.family.side m per):=
    (mul_le_mul_of_nonneg_right (le_abs_self a) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (below hu leaves) (abs_nonneg a))
  have fixed:Real.exp (-(((s/2)/2)*((n.val:ℝ)-d))/2)*A=A'*catchW (s/8) n:=by
    unfold A' catchW
    rw [mul_right_comm,←Real.exp_add]
    congr 2
    ring
  rw [fixed]
  exact (add_le_add (add_le_add (magnitude A' _ (by positivity) n size)
    (magnitude B _ (by positivity) X (dvd_trans size more)))
    (magnitude C _ (by positivity) n size)).trans budget.le

end YM.Integration.WilsonOriginalCensusOrbitPeriod
end

import YM.Integration.WilsonSeparatedPrefixMovingCapturedFees

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpIncome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D a k k' e u extra:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {E W K U V V' L:Credit}

open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingInvoice (Earned)
open scoped Classical

def gain {v:Rails h k u e}(Y:CutsP H T p v E W K U):ℝ:=
  trailC Y.ax.S Y.m Y.ceilC

theorem represented {v:Rails h k u e}(Y:CutsP H T p v E W K U):
    gain Y=(paceT Y.ax.S Y.m Y.ceilC)^((4:ℝ)⁻¹):=trail_ratio ..

theorem initial {v:Rails h k u e}(Y:CutsP H T p v E W K U)(C:Credit)(Z:ℝ)(licensed:Y.Age≤Z):
    price Y C 0 1≤gain Y*(C.buy Z*Y.fuel):=by
  have paid:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Credit.elder C Y.windowC.warm licensed) (trail_pos Y.ax.S Y.m Y.ceilC).le) Y.hf
  simpa only [WilsonIndependentMatchedCoverProfile.price,abs_one,one_mul,Nat.add_zero,gain,trailC,mul_left_comm,mul_assoc] using paid

theorem crossing {v:Rails h k u e}(Y:CutsP H T p v E W K U)(j extra:ℕ)(spare:0<extra):
    let x:=paceT Y.ax.S Y.m (Y.m+j)
    x^extra*trailC Y.ax.S (Y.m+j) Y.ceilC≤gain Y:=by
  intro x
  have xp:0<x:=pace_pos ..
  have x1:x≤1:=pace_le Y.ax.S (Nat.le_add_right _ _)
  have step:x^extra≤x:=by
    cases extra with
    | zero => omega
    | succ w =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ xp.le x1) xp.le).trans_eq (one_mul x)
  refine (mul_le_mul_of_nonneg_right step (trail_pos ..).le).trans ?_
  rw [show x=Real.exp (-(Y.ax.S.scale (Y.m+j)-Y.ax.S.scale Y.m)) from pace_rep ..]
  unfold gain trailC
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm:=scales Y.ax.S (Nat.le_add_right Y.m j)
  linarith

theorem ink {v:Rails h k u e}(Y:CutsP H T p v E W K U)(C:Credit)(j extra:ℕ)(spare:0<extra)
    (Z:ℝ)(licensed:Y.Age≤Z):
    let x:=paceT Y.ax.S Y.m (Y.m+j)
    (x^extra/gain Y)*price Y C j 1≤C.buy Z*Y.fuel:=by
  intro x
  have gp:0<gain Y:=trail_pos ..
  have cg:0≤C.buy Y.Age*Y.fuel:=mul_nonneg (zero_le_one.trans (C.purchase Y.windowC.warm)) Y.hf
  have bill:=mul_le_mul_of_nonneg_left (crossing Y j extra spare) cg
  change (C.buy Y.Age*Y.fuel)*(x^extra*trailC Y.ax.S (Y.m+j) Y.ceilC)≤(C.buy Y.Age*Y.fuel)*gain Y at bill
  have approved:=(mul_le_mul_of_nonneg_right (Credit.elder C Y.windowC.warm licensed) Y.hf)
  rw [div_mul_eq_mul_div,div_le_iff₀ gp]
  calc
    _ = (C.buy Y.Age*Y.fuel)*(x^extra*trailC Y.ax.S (Y.m+j) Y.ceilC):=by
      simp only [WilsonIndependentMatchedCoverProfile.price,abs_one,one_mul,trailC];ring
    _ ≤ _:=bill.trans (mul_le_mul_of_nonneg_right approved gp.le)

theorem mount {v:Rails h k u e}(Y:CutsP H T p v E W K U)(C:Credit)(j extra:ℕ)(spare:0<extra)
    (Z:ℝ)(licensed:Y.Age≤Z)(φ:Rarity D)(b:ℕ)(y r B:ℝ)
    (cap:radiusH φ (paceT Y.ax.S Y.m (Y.m+j)) y≤r)(invoice:Amplitude φ B):
    let x:=paceT Y.ax.S Y.m (Y.m+j)
    Earned Z C ((x^extra/gain Y)*((5*radiusH φ x y)^4*(9^b*(B*price Y C j 1))))
      ((5*r)^4*(9^b*(B*Y.fuel))):=by
  intro x
  have xp:0<x:=pace_pos ..
  have gp:0<gain Y:=trail_pos ..
  have rad:0≤radiusH φ x y:=zero_le_one.trans (fieldCap ..)
  have factor:0≤x^extra/gain Y:=div_nonneg (pow_nonneg xp.le _) gp.le
  have pp:0≤price Y C j 1:=by
    unfold WilsonIndependentMatchedCoverProfile.price
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (zero_le_one.trans (C.purchase Y.windowC.warm)) (Real.exp_pos _).le) Y.hf)
  have fee:=ink Y C j extra spare Z licensed
  have bb:=invoice.1
  refine ⟨by positivity,?_⟩
  calc
    _ = (5*radiusH φ x y)^4*(9^b*(B*((x^extra/gain Y)*price Y C j 1))):=by ring
    _ ≤ (5*r)^4*(9^b*(B*(C.buy Z*Y.fuel))):=by
      have nonneg:=mul_nonneg factor pp
      gcongr
    _ = _:=by ring

end YM.Integration.WilsonMovingForkSharpIncome

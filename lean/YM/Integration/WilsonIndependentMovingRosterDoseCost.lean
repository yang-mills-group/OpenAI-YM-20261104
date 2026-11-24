import YM.Integration.WilsonIndependentFittedReportedWage
import YM.Integration.WilsonIndependentMatchedRosterSlots

/-! Complete fee of the reported coordinate on each genuinely fitted slot. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterDoseCost
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedProxyIncome (cost tariff)
open WilsonIndependentMatchedRosterSlots (wallet)
open WilsonOriginalPublicPlantedStableCredit (span)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

/-- Only a fitted report uses the full forward matrix. -/
def stretch (flag:Bool)(h:ℕ)(δ:ℝ):ℝ:=if flag then 1 else (δ^h)⁻¹

lemma rate (X:CutsP H T p v E W K U):
    (Real.exp (span X X.i))^h=(paceT X.ax.S X.m X.ceilC ^ h)⁻¹:=by
  have hs:=WilsonIndependentMatchedCoverSum.spacing X.ax.S X.m X.i
  change Real.exp (-(span X X.i))=paceT X.ax.S X.m X.ceilC at hs
  rw [←hs,Real.exp_neg,inv_pow,inv_inv]

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u₀ e)(E W K U:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W K U)(a fee:ℝ),0<a → X.fuel=a*fee →
      cost e (dose X a⁻¹) ≤ C.buy X.Age*(fee*(paceT X.ax.S X.m X.ceilC ^ h)⁻¹):=by
  obtain ⟨A,bill⟩:=WilsonIndependentFittedReportedWage.original H T p v E W K U
  let n:ℝ:=((e+1:ℕ):ℝ)*(Fintype.card (Alma F):ℝ)
  let C:=(pur n).prodC A
  refine ⟨C,?_⟩
  intro X a fee pos fuel
  have nonneg:0 ≤ fee:=nonneg_of_mul_nonneg_right (fuel ▸ X.hf) pos
  have cast:|a⁻¹| * X.fuel=fee:=by rw [abs_of_pos (inv_pos.mpr pos),fuel,inv_mul_cancel_left₀ pos.ne']
  let δ:=paceT X.ax.S X.m X.ceilC
  have ds:0≤(δ^h)⁻¹:=inv_nonneg.mpr (pow_nonneg (pace_pos ..).le _)
  have An:0≤A.buy X.Age:=zero_le_one.trans (A.purchase X.windowC.warm)
  have row(j:ℕ)(hj:j≤e)(c:Alma F):
      ‖coeff j (dose X a⁻¹ c)‖ ≤ A.buy X.Age*(fee*(δ^h)⁻¹):=by
    have earned:=bill X a⁻¹ j hj c
    rw [cast,rate] at earned
    calc _≤_:=earned
         _=_:=by dsimp only [δ];ring
  unfold cost
  calc
    _≤∑_j∈range (e+1),∑_c:Alma F,A.buy X.Age*(fee*(δ^h)⁻¹):=
      sum_le_sum fun j hj=>sum_le_sum fun c _=>row j (Nat.le_of_lt_succ (mem_range.mp hj)) c
    _=n*(A.buy X.Age*(fee*(δ^h)⁻¹)):=by
      simp only [sum_const,card_range,card_univ,nsmul_eq_mul,n];ring
    _≤(pur n).buy X.Age*(A.buy X.Age*(fee*(δ^h)⁻¹)):=
      mul_le_mul_of_nonneg_right (pure_goal n X.Age) (mul_nonneg An (mul_nonneg nonneg ds))
    _=C.buy X.Age*(fee*(δ^h)⁻¹):=by rw [show C.buy X.Age=_ from Credit.products ..];ring

theorem masked (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u₀ e)(E W K U:Credit)
    (stable:Credit)(u b:ℕ):
    ∃M:Credit,∀(X:CutsP H T p v E W K U)(a fee:ℝ),0<a → X.fuel=a*fee → ∀flag:Bool,
      wallet flag X (dose X a⁻¹) (stable.buy X.Age*fee) u b ≤
        M.buy X.Age*(fee*stretch flag h (paceT X.ax.S X.m X.ceilC)):=by
  obtain ⟨C,paid⟩:=original H T p v E W K U
  let P:=tariff H T p e u b E W U
  let cost:=P.prodC C
  let M:=stable.prodC cost
  refine ⟨M,?_⟩
  intro X a fee pos fuel flag
  have nonneg:0 ≤ fee:=nonneg_of_mul_nonneg_right (fuel ▸ X.hf) pos
  have ap:1 ≤ stable.buy X.Age:=stable.purchase X.windowC.warm
  have bp:1≤cost.buy X.Age:=cost.purchase X.windowC.warm
  have both:M.buy X.Age=stable.buy X.Age*cost.buy X.Age:=Credit.products ..
  cases flag with
  | true =>
    change stable.buy X.Age*fee≤M.buy X.Age*(fee*1)
    rw [mul_one,both]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans ap) bp) nonneg
  | false =>
    let δ:=paceT X.ax.S X.m X.ceilC
    let gross:=fee*(δ^h)⁻¹
    have gw:0≤gross:=mul_nonneg nonneg (inv_nonneg.mpr (pow_nonneg (pace_pos ..).le _))
    change P.buy X.Age*WilsonIndependentMatchedProxyIncome.cost e (dose X a⁻¹) ≤ M.buy X.Age*gross
    calc
      _≤P.buy X.Age*(C.buy X.Age*gross):=mul_le_mul_of_nonneg_left (paid X a fee pos fuel)
        (zero_le_one.trans (P.purchase X.windowC.warm))
      _=cost.buy X.Age*gross:=by rw [show cost.buy X.Age=_ from Credit.products ..];ring
      _≤M.buy X.Age*gross:=mul_le_mul_of_nonneg_right (both ▸ le_mul_of_one_le_left (zero_le_one.trans bp) ap) gw

end YM.Integration.WilsonIndependentMovingRosterDoseCost


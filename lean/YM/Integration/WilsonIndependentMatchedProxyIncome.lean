import YM.Integration.WilsonIndependentMatchedReportedProxy
import YM.Integration.WilsonIndependentMatchedCoverCap

/-! The actual dressed reporting vector of the complete fitted peer pays its
held derivatives and scalar at every upper date on its own passport. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedProxyIncome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

open WilsonIndependentMatchedReportedProxy WilsonIndependentMatchedCoveredSeats
open WilsonIndependentMatchedSeatedIncome

def cost (e:ℕ)(d:Verse F):ℝ:=∑i ∈ Finset.range (e+1),∑j,‖coeff i (d j)‖
lemma nn (d:Verse F):0 ≤ cost e d:=Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))

lemma charged (d:Verse F)(i:ℕ)(hi:i ≤ e)(j:Alma F):‖coeff i (d j)‖ ≤ cost e d:=
  (Finset.single_le_sum (fun a _=>norm_nonneg (coeff i (d a))) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _=>Finset.sum_nonneg (fun b _=>norm_nonneg (coeff a (d b))))
      (Finset.mem_range.mpr (show i<e+1 by omega)))

def credit (H:Hol G)(T:SectionData F)(p:h<D)(e u:ℕ)(E W U:Credit):Credit:=
  (polarBill H T p e u E W U).choose

theorem row (X:CutsP H T p v E W K U)(d:Verse F)(i:ℕ)(hi:i ≤ X.i)(j:ℕ)(hj:j ≤ e)(r u:ℕ):
    Fruit 0 1 u ((polarP X.ax X.tx T p X.N X.m (X.m+i) d).2 j r)
      ((credit H T p e u E W U).buy X.Age*cost e d):=by
  let R:=X.vesselsC
  let δ:=max 0 (R.tempC (X.m+i) (X.m+i))
  have fee:Terms e (sectionSeal T p) (cost e d) δ d d:=
    fun j hj l=>twain.one _ _ (le_max_left ..) (charged d j hj l)
  have span:X.m+i ≤ X.N:=(Nat.add_le_add_left hi _).trans (X.hc.trans X.hn)
  exact (surSeen (passport X) X.ha (Nat.le_add_right _ _) le_rfl span span
    (WilsonIndependentMatchedCoverCap.house X i hi).2 (nn d) (le_max_right ..) d d fee u j hj r).wax

def tariff (H:Hol G)(T:SectionData F)(p:h<D)(e u b:ℕ)(E W U:Credit):Credit:=
  (credit H T p e (u+b) E W U).prodC (credit H T p e u E W U)

theorem original (X:CutsP H T p v E W K U)(φ:Rarity D)(d:Verse F)(y:ℝ)(o:CellR)
    (δ B:ℝ)(test:Amplitude φ B)(u b:ℕ):
    Funds X.vesselsC h h X.m X.i u b φ y o δ 0 ((tariff H T p e u b E W U).buy X.Age*cost e d) B
      (printed X.vesselsC (sectionSeal T p) φ d X.m X.N y o):=by
  let above:=credit H T p e (u+b) E W U
  let low:=credit H T p e u E W U
  let fee:=(tariff H T p e u b E W U).buy X.Age*cost e d
  have summed:fee=(above.buy X.Age*low.buy X.Age)*cost e d:=by rw [show fee=(above.prodC low).buy X.Age*cost e d by rfl,Credit.products]
  have h₁:1 ≤ above.buy X.Age:=above.purchase X.windowC.warm
  have h₂:1 ≤ low.buy X.Age:=low.purchase X.windowC.warm
  have a:above.buy X.Age*cost e d ≤ fee:=by rw [summed];exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans h₁) h₂) (nn d)
  have c:low.buy X.Age*cost e d ≤ fee:=by rw [summed];exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (zero_le_one.trans h₂) h₁) (nn d)
  have live:=wired X.vesselsC (sectionSeal T p) (passport X) φ d X.m X.N X.i X.ha
    (X.hc.trans X.hn) y o
  refine ⟨live.1,?_,?_,?_⟩
  · intro i hi
    let x:=paceT X.ax.S X.m (X.m+(i+1))
    have prices (j:ℕ)(hj:j ≤ e)(r:ℕ):Fruit 0 1 (u+b) ((polarP X.ax X.tx T p X.N X.m (X.m+(i+1)) d).2 j r) fee:=
      Award.more (row X d (i+1) hi j hj r (u+b)) a
    simp only [Real.rpow_zero,mul_one,printed,SealR.spins,FirstCharge,sectionSeal]
    exact (submitted _ (tournure X.L.L d (X.ha.trans (Nat.le_add_right _ _))
        ((Nat.add_le_add_left hi _).trans (X.hc.trans X.hn))) _ prices φ x y o h _
        (pace_pos ..) (pace_le _ (Nat.le_add_right _ _)) test)
  · intro i hi none
    exact WilsonIndependentMatchedVacant.absent _ φ _ y o h (pace_pos ..) none
  · have prices (j:ℕ)(hj:j ≤ e)(r:ℕ):Fruit 0 1 u ((polarP X.ax X.tx T p X.N X.m (X.m+0) d).2 j r) fee:=
      Award.more (row X d 0 (Nat.zero_le _) j hj r u) c
    simp only [Real.rpow_zero,mul_one,printed,SealR.spins,FirstCharge,sectionSeal,Nat.add_zero,pace_self]
    exact
      (WilsonIndependentMatchedCoverHome.placed _ (tournure X.L.L d X.ha ((Nat.le_add_right _ _).trans (X.hc.trans X.hn)))
        φ y o h fee B test prices).f_l

end YM.Integration.WilsonIndependentMatchedProxyIncome

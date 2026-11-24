import YM.Integration.WilsonIndependentFittedReportedWage
import YM.Integration.WilsonIndependentFittedPivotCash

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedStoppedWage
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonOriginalPublicPlantedStableCredit (span)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentFittedMixedCash (embed bill)
open WilsonIndependentFittedPivotCash (gross)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

def window (X:CutsP H T p v E W K U)(s:ℕ)(live:X.vesselsC.anchor≤ s)(older:s≤X.m):
    WindowS G (e+1) E:=⟨X.vesselsC,s,X.m-s,X.N,X.M,X.m,live,by omega,
      (Nat.le_add_right _ _).trans (X.hc.trans X.hn),(Nat.le_add_right _ _).trans (X.hc.trans X.hm)⟩
def numerical (X:CutsP H T p v E W K U)(s q:ℕ)(g:ℝ)(d:Verse F):ℝ:=
  ∑j,‖cash q g (embed (clock X.ax X.tx X.N X.m s (d j)))‖

theorem stored (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C V:Credit,∀(X:CutsP H T p v E W K U)(s:ℕ)(a:ℝ)(live:X.vesselsC.anchor≤ s)(older:s≤X.m),
      ∀j≤e,∀c:Alma F,
      ‖coeff j (clock X.ax X.tx X.N X.m s (dose X a c))‖≤
        C.buy (window X s live older).Age*((Real.exp (span X X.i))^h*V.buy X.Age*(|a| * X.fuel)):=by
  obtain ⟨V,reported⟩:=WilsonIndependentFittedReportedWage.original H T p v E W K U
  obtain ⟨C,paid⟩:=WilsonIndependentFittedKineticMass.original G h e E F
  refine ⟨C,V,fun X s a live older j hj c=>?_⟩
  have positive:0≤(Real.exp (span X X.i))^h*V.buy X.Age*(|a| * X.fuel):=
    mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (V.purchase X.windowC.warm)))
      (mul_nonneg (abs_nonneg _) X.hf)
  have receipt:=paid (window X s live older) (dose X a) _ positive (reported X a) j hj c
  have read:=WilsonIndependentFittedRelativeClock.reported X.ax X.tx X.N s (X.m-s) (dose X a c)
  rw [Nat.add_sub_of_le older] at read
  rw [read]
  exact receipt

theorem spent (X:CutsP H T p v E W K U)(s q:ℕ)(g:ℝ)(d:Verse F)(A:ℝ)
    (price:∀j≤q,∀c:Alma F,‖coeff j (clock X.ax X.tx X.N X.m s (d c))‖≤A):
    gross X s q g d≤numerical X s q g d+
      2*|g|^(q+1)*((Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*A):=by
  unfold gross numerical bill
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _≤∑_c:Alma F,∑_j∈Finset.range (q+1),A:=by
      apply Finset.sum_le_sum
      intro c _
      unfold WilsonPhysicalMarkedDefect.RawProduct.belt
      apply Finset.sum_le_sum
      intro j hj
      rw [embed, PowerSeries.coeff_map]
      change ‖(((coeff j (clock X.ax X.tx X.N X.m s (d c))):ℝ):ℂ)‖≤ A
      rw [Complex.norm_real]
      exact price j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) c
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Finset.card_range,nsmul_eq_mul];ring

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C V:Credit,∀(X:CutsP H T p v E W K U)(s:ℕ)(a g:ℝ)(live:X.vesselsC.anchor≤ s)(older:s≤X.m)
      (q:ℕ)(_cap:q≤e),
      gross X s q g (dose X a)≤numerical X s q g (dose X a)+2*|g|^(q+1)*
        ((Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*
          (C.buy (window X s live older).Age*((Real.exp (span X X.i))^h*V.buy X.Age*(|a| * X.fuel)))):=by
  obtain ⟨C,V,paid⟩:=stored H T p v E W K U
  exact ⟨C,V,fun X s a g live older q cap=>spent X s q g (dose X a) _ (fun j hj=>paid X s a live older j (hj.trans cap))⟩

end YM.Integration.WilsonIndependentFittedStoppedWage

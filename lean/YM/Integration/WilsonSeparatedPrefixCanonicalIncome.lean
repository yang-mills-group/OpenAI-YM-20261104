import YM.Integration.WilsonSeparatedPrefixCanonicalSoft
import YM.Integration.WilsonThermometerHostedCurrency
import YM.Integration.WilsonTrueProjectedLocatedTariff
import YM.Integration.WilsonTrueProjectedLocatedLeg

/-! Native polynomial cost of the masked original unary on the whole physical carrier. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalIncome
open Function Filter Finset Lattice RG Wilson Source Labels Marker Push QuadraticLocal MergeProof MergeProof.Accent
open Push.Local PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extra.Histories
open WilsonOriginalStarPrimaryCatalog WilsonRetainedMarkedInletRegular Trace.Physical.GermGraph
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

theorem coordinate {N p j d:ℕ}(jn:j≤N)(home:Opened (C) d j p)(o:Site ((C).side j p))
    (q:Coefficient ((C).labels.level d) ((C).side j p)){κ B X:ℝ}:
    let P:=(C).path.rep N p j
    let E:=(C).labels.level d
    q.Format o (C).params P → q.remBound o P κ B → d≤P.p.order → d≤P.p.power →
    E.coeffSize (Trace.Physical.Germ.projection E (C).params P.p.threshold o q)≤X → E.coeffSize q.x≤X+B:= by
  intro P E form bill ord pow head
  have hit:=WilsonTrueProjectedLocatedLeg.charge P o q form bill ord pow head
  have chart:=WilsonTrueProjectedLocatedTariff.chart R (W:=P) home rfl jn
  have maxFee:=le_trans (le_abs_self _) chart
  exact hit.trans (add_le_add le_rfl (le_trans (mul_le_mul_of_nonneg_right maxFee (rem_nonneg bill)) (one_mul B).le))

theorem original (d:ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (book:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀N p:ℕ, j≤N → (C).ref d≤j → ((A).params j).supportExponent=100 →
    ∀{V:Type},∀o:V → Site ((C).side j p),∀v:V,∀x:(C).label d,∀w:V → ℝ,0≤w v →
    ∀B:ℝ,0≤B →
    let P:=(C).path.rep N p j
    rent R N p j d o v x w (P.p.supportExponent-1)+cost P.p*(w v*B)≤
      w v*((H j)^6*(((C).labels.level d).coeffSize x)+(H j)^2*B) := by
  filter_upwards [WilsonThermometerSameWalkSectionFare.original R d simple pace book,
    WilsonThermometerSameWalkWindow.original R simple book] with j head reg N p live ref fixed V o v x w wp B bp P
  have budget:P.p=(A).budget j:=(R.makes.wilson.represents N p j live).vac
  have base:P.p.supportExponent=100:=by rw [budget];exact fixed
  have expo:rent R N p j d o v x w (P.p.supportExponent-1)≤rent R N p j d o v x w (100+1+1):=by
    unfold rent
    apply Finset.sum_le_sum
    intro i _
    have positive:0≤amount R N p j d o v x i:=by
      unfold amount
      split
      · exact norm_nonneg _
      · exact mul_nonneg (by unfold moving;positivity)
          (ActualRunPhysicalPages.priced R N p j d live ref (((C).labels.level d).core x) (o v)).2.1
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg wp positive)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by rw [base];norm_num) (Nat.cast_nonneg _))
  have cost0:0≤cost P.p:=by unfold cost;positivity
  have roof:= (reg p P budget 0).1
  have small:cost P.p≤(H j)^2:=(le_mul_of_one_le_left cost0 (Real.one_le_exp (by positivity))).trans roof
  calc _ ≤ (H j)^6*(w v*(((C).labels.level d).coeffSize x))+(H j)^2*(w v*B):=
            add_le_add (expo.trans (head N p live fixed o v x w wp)) (mul_le_mul_of_nonneg_right small (mul_nonneg wp bp))
       _ = _ := by ring

end YM.Integration.WilsonSeparatedPrefixCanonicalIncome
end

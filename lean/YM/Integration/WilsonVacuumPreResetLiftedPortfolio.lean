import YM.Integration.WilsonVacuumPreResetLiftedMoves

/-! The finite lifted catalogue has a true rooted tail, with separate fees
for the path length and the finite enumeration of the underlying currents. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedPortfolio
open Function Finset Set Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Filter
open Comparison.Density Comparison.Density.Render AnalyticBridge VerifiedReset Collection Quotes WilsonStartup
open RG01Estimate IterationFour.Vacuum Extra.Iteration Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Push.AbsoluteSums.Animals
open WilsonVacuumPreResetLiftedAgreement WilsonVacuumPreResetLiftedPiece WilsonVacuumPreResetLiftedSite
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetLiftedFolio
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}

open WilsonVacuumPreResetPeriodIndex WilsonVacuumPreResetPeriodCatalogue

theorem live (B:BudgetPoint)(σ C:ℝ)(k:ℕ→ℕ→ℝ)(Z:SeriesA G)(t q:ℕ):
    let A:=entries n B σ C Z k
    ∀i,A.E i≠0→(i∈WilsonVacuumPreResetLiftedFolio.selected n t q Z ↔
      depth n Z i<t ∧ WilsonVacuumPreResetLiftedSeries.length n Z i≤q):=by
  induction Z with
  | nil=>intro A i e;exact (e rfl).elim
  | cons a tail ih=>
    intro A i e
    obtain ⟨j,rfl⟩:=Payload.coding.symm.surjective i
    cases j with
    | inl j=>
      have old:(entries n B σ C tail k).E j≠0:=by
        simpa [A,entries,tally,IterationFour.Vacuum.Render.adorn,Payload.attach] using e
      simpa [WilsonVacuumPreResetLiftedFolio.selected,depth,WilsonVacuumPreResetLiftedSeries.length] using ih j old
    | inr j=>
      simp [WilsonVacuumPreResetLiftedFolio.selected,depth,WilsonVacuumPreResetLiftedSeries.length,seats,legs]

theorem original (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:preExponent B/B.B≤σ/4)(blocks:2≤B.B)(Z:SeriesA G)(draw:Draw Z σ C)
    (k:ℕ→ℕ→ℝ)(q:ℕ){η:ℝ}(ep:0<η):
    ∀ᶠt:ℕ in atTop,let M:=WilsonVacuumPreResetLiftedRack.model n B σ C k Z t q
      Precise.Suggests B M (rebate σ (q+1)*M.bill+η) M.bill:=by
  let A:=entries n B σ C Z k
  let X:Listing G n:=⟨A.reg,A.forced⟩
  have funded:=(WilsonVacuumPreResetPeriodEntries.original simple hn B hs reach blocks Z draw k).1
  have tail:=WilsonVacuumPreResetLiftedSeries.original simple hn B hs reach blocks Z draw (q+1) k
  let omitted (t i:ℕ):Prop:=WilsonVacuumPreResetLiftedSeries.length n Z i≤q ∧ t≤depth n Z i
  have sale:=Caddy.limits (A:=X) B omitted A.E funded (fun i _=>
    (eventually_gt_atTop (depth n Z i)).mono (fun t ht h=>(not_le_of_gt ht) h.2)) ep
  filter_upwards [sale] with t ht
  let M:=WilsonVacuumPreResetLiftedRack.model n B σ C k Z t q
  let selected:=WilsonVacuumPreResetLiftedFolio.selected n t q Z
  have err:M.trunk-M.pioneers=(fun i=>if q+1≤WilsonVacuumPreResetLiftedSeries.length n Z i then A.E i else 0)+
      (fun i=>if omitted t i then A.E i else 0):=by
    funext i
    change A.E i-submitted A selected i=_
    simp only [Pi.add_apply,submitted]
    by_cases nz:A.E i=0
    · by_cases h:i∈selected <;> simp [h,nz]
    have covered:i∈selected ↔ depth n Z i<t ∧ WilsonVacuumPreResetLiftedSeries.length n Z i≤q:=live B σ C k Z t q i nz
    by_cases late:depth n Z i<t <;> by_cases nearby:WilsonVacuumPreResetLiftedSeries.length n Z i≤q <;>
      simp [covered,late,nearby,omitted,show t≤depth n Z i ↔ ¬depth n Z i<t from not_lt.symm,
        show q+1≤WilsonVacuumPreResetLiftedSeries.length n Z i ↔ ¬WilsonVacuumPreResetLiftedSeries.length n Z i≤q by omega]
  refine ⟨funded,?_,?_,WilsonVacuumPreResetLiftedMoves.moves B σ C Z k t q⟩
  · convert Acquire.budget_cut (fun i=>i∈selected) funded using 1 <;> first|rfl|skip
    funext i
    change submitted A selected i=_
    by_cases h:i∈selected <;> simp [submitted,h]
    rfl
  · change Meadow.Budget B A.reg (M.trunk-M.pioneers) _
    rw [err]
    apply Abacus.pay_bundle B tail
    convert ht using 1
    funext i
    by_cases e:omitted t i <;> simp [e]

end YM.Integration.WilsonVacuumPreResetLiftedPortfolio

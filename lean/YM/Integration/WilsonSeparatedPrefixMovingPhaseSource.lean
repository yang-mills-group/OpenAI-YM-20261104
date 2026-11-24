import YM.Integration.WilsonSeparatedPrefixMovingExteriorRemainder
import YM.Integration.WilsonSeparatedPrefixMovingOwnDate

/-! The omitted spatial Taylor terms have their own actual passport and a
single rooted fare on the original exterior tower, including rank zero. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPhaseSource
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout
open WilsonSeparatedPrefixMovingExteriorTaylor (sectionAt)
open WilsonSeparatedPrefixMovingExteriorRemainder (remainder)
open WilsonSeparatedPrefixMovingProfileDerivatives (cut)
open WilsonSeparatedPrefixMovingExteriorTranslation (moved)
open WilsonIndependentMatchedCoverProfile (charge Income)
open WilsonSeparatedPrefixMovingOwnDate (fee)
variable {G:Gauge}{D k e:ℕ}{H:Hol G}{C₂ C C₁:Credit}{R:Realm G (e+1) C}{Q:SealR G}
private def point (x:Point4):Scroll D→ₗ[ℝ]ℝ where
  toFun:=fun p=>p.val x
  map_add':=by intros;rfl
  map_smul':=by intros;rfl
theorem footprint (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(y:ℝ)(z o:CellR)(L:ℕ):
    tsupport (remainder φ hf y z o L).ψ.val ⊆ tsupport (moved φ y z o).ψ.val ∪ tsupport φ.ψ.val:=by
  apply closure_minimal _ ((isClosed_tsupport _).union (isClosed_tsupport _))
  intro x hx;by_contra outside
  have absent:point x (moved φ y z o).ψ=0:=by
    by_contra live;exact outside (Or.inl (subset_closure live))
  have gone (n:ℕ)(w:Fin n→Axis):point x (cut φ hf w).ψ=0:=by
    by_contra live;exact outside (Or.inr (crestShelter x live))
  change point x (_-WilsonSeparatedPrefixMovingExteriorRemainder.folded φ hf y z o L)≠0 at hx
  simp [map_sub,WilsonSeparatedPrefixMovingExteriorRemainder.folded,map_sum,map_smul,gone,absent] at hx
theorem original (Q:SealR G)(φ:Rarity (Q.D+k+1))(hf:ContDiff ℝ ∞ φ.ψ.val):
    ∃M:ℝ,0 ≤ M ∧ ∀(_fund:PassportC H R Q C₁ C₂)(t i N u:ℕ)(_origin:R.anchor ≤ t)
      (_after:t ≤ i)(_cap:i ≤ N)(Z:ℝ)(_clock:Compar R.draws.S R.y t i ≤ Z)
      (X:Q.Rider)(y:ℝ)(z o:CellR)(P:Patch),
      let ψ:=remainder (sectionAt φ) hf y z o k
      let x:=paceT R.draws.S t i
      let α:=(polarBill H Q.ans Q.path e u C C₁ C₂).choose
      ψ.radius ≤ φ.radius+|y| ∧
      Income (locale o (Q.spins R.draws R.paid ψ t i N y X)) Q.h e u (OrbP P ψ x y o)
        ((x^Q.h)⁻¹*((5*radiusH ψ x y)^4*(9^u*((M*|y|^(k+1))*(α.buy Z*fee Q e X))))):=by
  obtain ⟨M,hm,amount⟩:=WilsonSeparatedPrefixMovingExteriorRemainder.original φ hf
  refine ⟨M,hm,?_⟩
  intro fund t i N u origin after cap Z clock X y z o P ψ x α
  refine ⟨WilsonSeparatedPrefixMovingExteriorRemainder.radius (sectionAt (D:=Q.D) (k:=k) φ) hf y z o k,?_⟩
  rw [←WilsonSeparatedPrefixMovingOwnDate.units]
  exact WilsonSeparatedPrefixMovingOwnDate.column fund t i N u origin after cap Z clock X ψ y o P _ (amount y z o)
end YM.Integration.WilsonSeparatedPrefixMovingPhaseSource

import YM.Integration.WilsonSeparatedPrefixMovingPhasePolynomial

/-! Cartesian expansion of every funded low derivative of the actual
translated exterior stencil on the original child and common center. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPhaseStencil
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)

open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingExteriorTaylor (sectionAt jet)
open WilsonSeparatedPrefixMovingCenterMoments (monomial)
variable {D k:ℕ}

def term (f:Point4→ℝ)(x:Point4)(a:ℝ)(z o:CellR)(n:ℕ):ℝ:=
  (n.factorial:ℝ)⁻¹*a^n*∑w:Fin n→Axis,
    monomial o w z*iteratedFDeriv ℝ n f x (Embroider.dot ∘ w)

theorem original (φ:Rarity (D+k+1)):
    ∃ M:ℝ,0≤M ∧ ∀j,∀hj:j≤D,∀(axes:Fin j→Axis)(ε y:ℝ)(_positive:0≤ε)(_fine:ε≤1)
      (root:Cover)(z o u:CellR),let x:=Mer.address ε y o root u.val
            let page:=wheelC ε y root (sectionAt φ).ψ z
      ‖page.val ⟨⟨j,Nat.lt_succ_of_le hj⟩,axes⟩ u-ε^j*∑n∈Finset.range (k+1),term (crease φ.ψ axes) x (-y) z o n‖≤M*|y|^(k+1):=by
  obtain ⟨M,nn,early⟩:=WilsonSeparatedPrefixMovingExteriorTaylor.original φ
  obtain ⟨_,_,smooth⟩:=WilsonSeparatedPrefixMovingExteriorTaylor.wallet φ
  refine ⟨M,nn,?_⟩
  intro j hj axes ε y pos fine root z o u x
  have raw:=early j hj axes ε y pos fine root z o u
  dsimp only at raw
  have finite:=WilsonSeparatedPrefixMovingPhasePolynomial.original (crease φ.ψ axes)
    (((smooth j hj axes).1).of_le (by exact_mod_cast (show k ≤ k+1 by omega))) x (-y) z o
  rw [neg_smul] at finite
  simpa only [term] using (finite ▸ raw : _)

end YM.Integration.WilsonSeparatedPrefixMovingPhaseStencil

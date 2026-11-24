import YM.Integration.WilsonSeparatedPrefixMovingProfileDerivatives

/-! The complete translated test belongs to the native Volume. Its Taylor
terms come from compact derivatives of that same exterior on the held child. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingExteriorVolume
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout
open WilsonSeparatedPrefixMovingExteriorTaylor (sectionAt)
open WilsonSeparatedPrefixMovingPhaseStencil (term)
open WilsonSeparatedPrefixMovingCenterMoments (monomial)
open WilsonSeparatedPrefixMovingProfileDerivatives (cut)
variable {D k j:ℕ}
def observe (i:Knob D)(u:CellR):Volume D→ₗ[ℝ]ℝ where
  toFun:=fun p=>p.val i u
  map_add':=by intros;rfl
  map_smul':=by intros;rfl
def layer (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(ε y:ℝ)(root:Cover)(z o:CellR)(n:ℕ):Volume D:=
  ((n.factorial:ℝ)⁻¹*(-y)^n) • ∑w:Fin n→Axis,
    monomial o w z • wheelC ε y root (cut φ hf w).ψ o
def printed (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(ε y:ℝ)(root:Cover)(z o:CellR)(L:ℕ):Volume D:=
  ∑n∈Finset.range (L+1),layer φ hf ε y root z o n
theorem slot (φ:Rarity D)(ε y:ℝ)(root:Cover)(o u:CellR)(j:ℕ)(hj:j≤D)(b:Fin j→Axis):
    observe ⟨⟨j,Nat.lt_succ_of_le hj⟩,b⟩ u (wheelC ε y root φ.ψ o)
      = ε^j*crease φ.ψ b (Mer.address ε y o root u.val):=currentP ε y o root φ.ψ b hj u.val
theorem coefficient (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(ε y:ℝ)(root:Cover)
    (z o u:CellR)(n j:ℕ)(hj:j≤D)(b:Fin j→Axis):
    observe ⟨⟨j,Nat.lt_succ_of_le hj⟩,b⟩ u (layer φ hf ε y root z o n)
      =ε^j*term (crease φ.ψ b) (Mer.address ε y o root u.val) (-y) z o n:=by
  rw [layer,map_smul,map_sum];simp only [map_smul,smul_eq_mul]
  have seen (w:Fin n→Axis):observe ⟨⟨j,Nat.lt_succ_of_le hj⟩,b⟩ u
       (wheelC ε y root (cut φ hf w).ψ o)=ε^j*iteratedFDeriv ℝ n (crease φ.ψ b)
          (Mer.address ε y o root u.val) (Embroider.dot ∘ w):=(slot (cut φ hf w) ε y root o u j hj b).trans
            (congr_arg (ε^j*·) (WilsonSeparatedPrefixMovingProfileDerivatives.original φ hf w b _).symm)
  simp_rw [seen]
  unfold term
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro w _;ring
theorem original (φ:Rarity (D+k+1))(hf:ContDiff ℝ ∞ φ.ψ.val):
    ∃ M:ℝ,0≤M ∧ ∀(ε y:ℝ)(_positive:0≤ε)(_fine:ε≤1)(root:Cover)(z o:CellR),
      ‖wheelC ε y root (sectionAt (D:=D) (k:=k) φ).ψ z-printed (sectionAt (D:=D) (k:=k) φ) hf ε y root z o k‖≤M*|y|^(k+1):=by
  obtain ⟨M,hm,book⟩:=WilsonSeparatedPrefixMovingPhaseStencil.original φ
  refine ⟨M,hm,?_⟩
  intro ε y pos fine root z o
  apply vote_cap _ (mul_nonneg hm (pow_nonneg (abs_nonneg _) _))
  intro addr u;rcases addr with ⟨⟨j,hj⟩,b⟩
  have smooth0:ContDiff ℝ ∞ (sectionAt (D:=D) (k:=k) φ).ψ.val:=hf
  have paid:=book j (Nat.le_of_lt_succ hj) b ε y pos fine root z o u
  change ‖observe _ u (_-printed (sectionAt (D:=D) (k:=k) φ) hf ε y root z o k)‖≤_
  rw [map_sub,printed,map_sum]
  simp_rw [coefficient (sectionAt (D:=D) (k:=k) φ) smooth0 ε y root z o u _ j (Nat.le_of_lt_succ hj) b]
  rw [←Finset.mul_sum]
  exact paid
end YM.Integration.WilsonSeparatedPrefixMovingExteriorVolume

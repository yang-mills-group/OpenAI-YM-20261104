import YM.Integration.WilsonMSbarCorrelationHeatAllocation
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneMeasuredCorrelationEstimates

set_option autoImplicit false
noncomputable section

namespace YangMills.Matching.CorrelationOnly

open Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g} {T : Hierarchy C}

/-- The compact, spatial derivative and tested correlation estimates on one public field. -/
structure FiledCorrelations (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) : Prop where
  jets : ShapeIncome M S H
  compact (n p : ℕ) (d : Fin n → ℕ) (o : Spacetime) (K : Set (Points n))
      (_compact : IsCompact K) (_separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ phase : Option T.Character,
      ∀ (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      ‖correlationError M S H p (fun i => ⟨d i, v i⟩) phase o s x‖ ≤
        A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1)
  tested (n : ℕ) (d : Fin n → ℕ) (phase : Option T.Character)
      (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) :
    let a : Fin n → Label B := fun i => ⟨d i,v i⟩
    HasExpansion 0 H.clock (fun s x => T.correlation phase (H.inputs s a)
      (WithLp.toLp 2 fun i => o + s • x i)) (fun k x => S.correlation M k a x)

theorem groupFiledCorrelationsOfShape (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) (shapes : ShapeIncome M S H) : FiledCorrelations M S H where
  jets := shapes
  compact n p d o K hK separated := by
    obtain ⟨A,hA,late⟩ := shapes n p 0 d K hK separated
    exact ⟨A,hA,late.mono fun s hs phase v x hx => shapeValue (hs phase v o x hx)⟩
  tested n d phase v o := by
    apply testedOfShapeJets H.positive (clockAtZero H)
    intro p K hK separated
    obtain ⟨A,hA,late⟩ := shapes n p 0 d K hK separated
    refine ⟨A * (∏ i, sectorMass (v i)),
      mul_nonneg hA (Finset.prod_nonneg fun i _ => sectorMass_nonneg (v i)), ?_⟩
    exact late.mono fun s hs x hx => hs phase v o x hx

variable {M N : YangMills.MSbar.Coefficients B}

def FiledSeparatedRead (M N : YangMills.MSbar.Coefficients B) : Prop :=
  ∀ {n : ℕ} (k : ℕ) (v : Fin n → Label B) (x : YangMills.Points n),
    x ∈ YangMills.separated n → M.correlation n k v x = N.correlation n k v x

theorem filedConvertedAt (read : FiledSeparatedRead M N) (S : Conversion B) {n : ℕ}
    (k : ℕ) (v : Fin n → Label B) (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    S.correlation M k v x = S.correlation N k v x := by
  rw [allocated S M k v x, allocated S N k v x]
  apply Finset.sum_congr rfl
  intro heat _
  apply Finset.sum_congr rfl
  intro j _
  rw [read j.val (S.inputs v heat) x hx]

private theorem transportFiledJet {n j : ℕ} {a b c d : Points n → ℂ} {x : Points n} {D : ℝ}
    (field : a =ᶠ[𝓝 x] c) (reading : b =ᶠ[𝓝 x] d)
    (price : YangMills.Matching.shapeJetEstimateAt j a b x D) :
    YangMills.Matching.shapeJetEstimateAt j c d x D := by
  refine ⟨price.1.congr_of_eventuallyEq field.symm, price.2.1.congr_of_eventuallyEq reading.symm, ?_⟩
  intro k hk
  have equal : (fun y => a y - b y) =ᶠ[𝓝 x] (fun y => c y - d y) := field.sub reading
  rw [← (equal.iteratedFDeriv ℝ k).eq_of_nhds]
  exact price.2.2 k hk

theorem filedCorrelationsOnSeparated (S : Conversion B) (H : Measurement B T)
    (read : FiledSeparatedRead M N) (priced : FiledCorrelations M S H) :
    FiledCorrelations N S H := by
  apply groupFiledCorrelationsOfShape
  intro n p j d K compact separated
  obtain ⟨A, positive, late⟩ := priced.jets n p j d K compact separated
  refine ⟨A, positive, late.mono ?_⟩
  intro s income phase v o x hx
  refine transportFiledJet
    Filter.EventuallyEq.rfl ?_ (income phase v o x hx)
  filter_upwards [(YangMills.separated n).isOpen.mem_nhds (separated hx)] with y hy
  apply Finset.sum_congr rfl
  intro k _
  rw [filedConvertedAt read S k.val _ y hy]

end YangMills.Matching.CorrelationOnly


import YM.Integration.WilsonCenteredNestedRawPair

/-! Evaluate the same public terminal coordinate as one Haar and real
average of the original raw field.  No rotation is chosen at an
individual intermediate channel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRootMean
open Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription MeasureTheory
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRealOrbit
open scoped Classical Topology BigOperators
attribute [local instance] measO borelO YM.Work.A15.compact_ortho
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}

lemma own (m : ℕ) (w : S.Field m) : Q.cutTest m m w = Q.knife m w := by
  rw [Q.test_formula m m le_rfl,←Q.knife_apply m m (h:=le_rfl) w,F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts w]

theorem checked (m : ℕ) (c : Q.channels m) (x : I→E4) (o : E4) (v : Labels S d) :
    read F Q m m c (checkReal Q.port Q.law Q.continuum m x o v) = Q.coef m c x v o := by
  let z : Q.stratum m := ⟨Q.fresh m x o v,Q.fresh_mem m x o v⟩
  unfold WilsonCenteredNestedProjectedShadow.read
  simp only [LinearMap.comp_apply,own]
  change (Q.basis m).coord c ((Q.stratum m).subtype.leftInverse z.val) = (Q.basis m).coord c z
  exact congrArg ((Q.basis m).coord c) (LinearMap.leftInverse_apply_of_inj (Q.stratum m).ker_subtype z)

lemma checkable (m : ℕ) (x : I→E4) (o : E4) (hint : orbitMargin Q.port m x o) (v : Labels S d) :
    Integrable (fun k=>spinning Q.port F.sector.turns m x o k v) haar := by
  simp_rw [Orbits.scatter Q.port Q.continuum m]
  exact integrable_finsetSum (μ:=haar) (f:=fun j=>bears F.sector.turns Q.port j m x o v) (bands F.sector.derivatives m) (fun j inJ=>integrable_bears Q.port Q.law Q.continuum m x o j v (hint j inJ))

/-- Simultaneous rotation and real projection after all held child fields
have been supplied. The terminal truncation here is the requested
output grade itself, including zero. -/
theorem original (m : ℕ) (c : Q.channels m) (x : I→E4) (o : E4)
    (hint : orbitMargin Q.port m x o) (v : Labels S d) :
    Q.coef m c x v o =
      (2:ℝ)⁻¹ • ((∫ k, read F Q m m c (restored F Q.port m x v o k false) ∂haar) +
                   ∫ k, read F Q m m c (restored F Q.port m x v o k true) ∂haar) := by
  let L := ((read F Q m m c).toContinuousLinearMap).restrictScalars ℝ
  let J := (conjugateR F.room.kernel.spin m).toContinuousLinearMap
  have h0 := checkable F Q m x o hint v
  have h1 := checkable F Q m x o hint (bar F.room.kernel.spin v)
  rw [←checked F Q m c x o v,checkValue]
  change L ((2:ℝ)⁻¹ • (averageV Q.port F.sector.turns m x o v + J (averageV Q.port F.sector.turns m x o (bar F.room.kernel.spin v)))) = _
  rw [map_smul,map_add]
  unfold averageV
  simp only [if_pos hint]
  rw [←L.integral_comp_comm h0,←J.integral_comp_comm h1,←L.integral_comp_comm (J.integrable_comp h1)]
  rfl

end YM.Integration.WilsonCenteredNestedRootMean

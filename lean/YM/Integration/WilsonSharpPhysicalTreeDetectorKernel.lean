import YM.Integration.WilsonCenteredNestedRotation
import YM.OPE.Nesting.Sensors
import YM.OPE.Orbits.Continuity

/-! The finite detector of the elected packet. Its input coordinates are physical
correlations with fixed basis labels at the rotated exterior positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeDetectorKernel
open Function Filter Set MeasureTheory Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription WilsonCenteredNestedShadowBasis
open scoped Classical Topology BigOperators ContDiff
attribute [local instance] Orbits.measO Orbits.borelO Orbits.hμ YM.Work.A15.compact_ortho
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

abbrev Probe (h : ℕ) := Σ n : Fin (h+1), Σ i : ↥(bands F.sector.derivatives n.val),
  Σ e : ↥(Q.port.sheet i.val).support, Slot S (expo e.val)

abbrev Signals (h : ℕ) := Probe F Q h → C(Ortho, ℂ)

/-- Multiply a scalar signal pointwise by a continuous vector-valued kernel. -/
def multiplySignal {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (g : C(Ortho,V)) : C(Ortho,ℂ) →L[ℝ] C(Ortho,V) := by
  let L : C(Ortho,ℂ) →ₗ[ℝ] C(Ortho,V) := {
    toFun := fun u => ⟨fun k => u k • g k, u.continuous.smul g.continuous⟩
    map_add' := fun u w => ContinuousMap.ext fun k => add_smul (u k) (w k) (g k)
    map_smul' := fun a u => ContinuousMap.ext fun k => smul_assoc a (u k) (g k) }
  apply L.mkContinuous ‖g‖
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro k
  change ‖u k • g k‖ ≤ _
  rw [norm_smul,mul_comm ‖g‖]
  exact mul_le_mul (u.norm_coe_le_norm k) (g.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg _)

def starSignal : C(Ortho,ℂ) →L[ℝ] C(Ortho,ℂ) := by
  let L : C(Ortho,ℂ) →ₗ[ℝ] C(Ortho,ℂ) := {
    toFun := fun u => ⟨fun k => star (u k),u.continuous.star⟩
    map_add' := fun u w => ContinuousMap.ext fun k => star_add (u k) (w k)
    map_smul' := fun a u => ContinuousMap.ext fun k => by
      change star (a • (u k)) = a • star (u k)
      simp }
  apply L.mkContinuous 1
  intro u
  rw [one_mul]
  exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun k => (norm_star (u k)).le.trans (u.norm_coe_le_norm k))

/-- Haar integration on the compact physical rotation group has norm at most one. -/
def haarReader {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    C(Ortho,V) →L[ℝ] V := by
  let L : C(Ortho,V) →ₗ[ℝ] V := {
    toFun := fun u => ∫ k, u k ∂haar
    map_add' := fun u w => integral_add (u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    map_smul' := fun a u => integral_smul a _ }
  apply L.mkContinuous 1
  intro u
  change ‖∫ k, u k ∂haar‖ ≤ 1 * ‖u‖
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,one_mul] using
    (norm_integral_le_of_norm_le_const (μ:=haar) (Eventually.of_forall u.norm_coe_le_norm))

private lemma coeff_cont {J : Type} [Fintype J] {d : J → ℕ} (z : Ortho → Labels S d)
    (hz : ∀ j, Continuous (fun k => z k j)) (t : Slot S d) : Continuous (fun k => coeff (z k) t) := by
  apply continuous_finsetProd
  intro j _
  exact ((Module.finBasis ℂ (S.Field (d j))).coord (t j)).continuous_of_finiteDimensional.comp (hz j)

/-- The fixed kernel contains every moving basis coordinate, including the real branch. -/
def kernel (n : ℕ) (i : Mode F.sector.derivatives) (e : Exterior C.book) (t : Slot S (expo e))
    (tint : Bool) : C(Ortho,S.Field n) := by
  let w := fun k => turnsPort F.sector.turns k e
  have hw (j : Fin e.n) : Continuous (fun k => w k j) := Q.law.spin _ _
  let wb := fun k => bar F.room.kernel.spin (w k)
  have hb (j : Fin e.n) : Continuous (fun k => wb k j) :=
    (conjugateR F.room.kernel.spin (expo e j)).continuous_of_finiteDimensional.comp (hw j)
  let a := fun k => if tint then star (coeff (wb k) t) else coeff (w k) t
  have hc : Continuous a := by
    cases tint
    · exact coeff_cont w hw t
    · exact (coeff_cont wb hb t).star
  exact ⟨fun k => ((Q.port.sheet i) e * a k) • F.sector.turns.act n k (Q.port.loaded i n),
    (continuous_const.mul hc).smul (Q.law.spin _ _)⟩

/-- Sum the actual port sheets, with grade `n` fixed before choosing a rotation. -/
def spinReader (h : ℕ) (n : Fin (h+1)) (tint : Bool) : Signals F Q h →L[ℝ] C(Ortho,S.Field n.val) :=
  ∑ i : ↥(bands F.sector.derivatives n.val), ∑ e : ↥(Q.port.sheet i.val).support, ∑ t : Slot S (expo e.val),
    (multiplySignal (kernel F Q n.val i.val e.val t tint)).comp
      ((if tint then starSignal else ContinuousLinearMap.id ℝ _).comp
        (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Probe F Q h => C(Ortho,ℂ)) ⟨n,i,e,t⟩))

/-- All grades from zero through the requested horizon are independently tested, cut and raised. -/
def reader (h : ℕ) : Signals F Q h →L[ℝ] S.Field h :=
  ∑ n : Fin (h+1),
    let cut := (F.sector.derivatives.rise (d:=n.val) (Nat.le_of_lt_succ n.isLt)).comp (Q.knife n.val)
    (cut.toContinuousLinearMap.restrictScalars ℝ).comp
      ((2:ℝ)⁻¹ • (haarReader.comp (spinReader F Q h n false) +
        (conjugateR F.room.kernel.spin n.val).toContinuousLinearMap.comp
          (haarReader.comp (spinReader F Q h n true))))

theorem bounded (h : ℕ) (u : Signals F Q h) : ‖reader F Q h u‖ ≤ ‖reader F Q h‖ * ‖u‖ :=
  (reader F Q h).le_opNorm u

end YM.Integration.WilsonSharpPhysicalTreeDetectorKernel

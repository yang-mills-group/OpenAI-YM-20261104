import YM.Integration.FVA1Physical.Round2.VoiceBank
import YM.Integration.FVA1Physical.Wilson.BatchHistory

/-! One fixed tensor bank gives every actual mixed stencil, allowing an
independent test in the unit coefficient ball at each input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Finset Lattice RG YM.Wilson Source LocalLTE.Sail Extra.Histories Labels
open Tree Precision PertExtension PertExtension.Chart
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Spool
open scoped Classical BigOperators ContDiff
variable {I : Type} {G : Gauge} {N n : ℕ} {H : History G} (Y : Batch H N n I) (s : Finset I)

abbrev AxisTuple := (i : ↥s) → VoiceAxis ((frames G).level (Y.demand i))
def tensorWeight (v : ∀ i, ((frames G).level (Y.demand i)).Coeff) (t : AxisTuple Y s) : ℝ :=
  ∏ i : ↥s, axisWeight _ (v i) (t i)
def axisPayoff (t : AxisTuple Y s) (U : Config G (H.S.side N n)) : ℂ :=
  ∏ i : ↥s, primProbe H N n (axisVoice ((frames G).level (Y.demand i)) (t i))
    (Y.motion i) (fun j=>Y.origin j i) U
def retest (v : ∀ i, ((frames G).level (Y.demand i)).Coeff) : Batch H N n I := {Y with voice := v}

theorem tensorWeight_bounded (v : ∀ i, ((frames G).level (Y.demand i)).Coeff)
    (bound : ∀ i, ((frames G).level (Y.demand i)).coeffSize (v i) ≤ 1) (t : AxisTuple Y s) :
    |tensorWeight Y s v t| ≤ 1 := by
  rw [tensorWeight,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _=>abs_nonneg _) fun i _=>axisWeight_bounded _ (bound i) (t i)

theorem tested_product_axes (v : ∀ i, ((frames G).level (Y.demand i)).Coeff)
    (U : Config G (H.S.side N n)) :
    fullProduct (retest Y v).wavelengths s U = ∑ t,tensorWeight Y s v t • axisPayoff Y s t U := by
  unfold fullProduct
  rw [←Finset.prod_attach]
  change (∏ i : ↥s, primProbe H N n (v i) (Y.motion i) (fun j=>Y.origin j i) U) = _
  calc
    _ = ∏ i : ↥s, ∑ a, axisWeight ((frames G).level (Y.demand i)) (v i) a •
        primProbe H N n (axisVoice _ a) (Y.motion i) (fun k=>Y.origin k i) U :=
      prod_congr rfl fun i _=>wavelength_axes H N n (Y.motion i) (fun k=>Y.origin k i) U (v i)
    _ = _ := ?_
  simp only [Complex.real_smul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [prod_mul_distrib,tensorWeight,axisPayoff,Complex.ofReal_prod]

theorem axes_witnessed (t : AxisTuple Y s) (L : ℂ →L[ℝ] ℝ) :
    Continuous (axisPayoff Y s t) ∧ GaugeInvariant (axisPayoff Y s t) ∧
    ContDiffAt ℝ ω ((L ∘ axisPayoff Y s t) ∘ expLinks G (Edge (Site (H.S.side N n)))) 0 := by
  let b : Batch H N n (↥s) := ⟨fun i=>Y.demand i,fun i=>axisVoice _ (t i),
    fun i=>Y.motion i,fun m i=>Y.origin m i⟩
  have W i := Wilson.wavelength_witnessed H N n b i
  exact ⟨continuous_finsetProd _ fun i _=>(W i).1,
    fun k v=>Finset.prod_congr rfl fun i _=>(W i).2.1 k v,
    L.contDiff.contDiffAt.comp 0 (contDiffAt_prod (fun i _=>(W i).2.2))⟩
end YM.Integration.FVA1Physical.Round2

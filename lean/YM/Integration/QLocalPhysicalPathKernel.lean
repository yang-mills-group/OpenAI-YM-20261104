import YM.Integration.ActualWilsonConditionalRoots
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.WithDensity

/-! The common physical path visits the actual Wilson fibres up to its
genuine finite upper regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalPathKernel
open Function Finset Set MeasureTheory ProbabilityTheory Lattice Wilson RG OPE.Therm
open ActualWilsonConditionalRoots
open scoped ENNReal Topology Classical
variable {G : Gauge} (C : Family G) {N p m : ℕ}
local notation "X" k => Config G (C.side k p)
local notation "μ" k => scene C.path N p k

def next (N p m : ℕ) : Kernel (Config G (C.side m p)) (Config G (C.side (m+1) p)) :=
  (Kernel.const _ (prior G _)).withDensity (fun V U=>ENNReal.ofReal (actualConditionalDensity C N p m V U))

theorem held (hC : C.Makes) (hm : m < N) (V : X m) :
    next C N p m V=fibre C (N:=N) V := by
  have ht : Measurable (uncurry (fun (V : X m) (U : X (m+1)) =>
      ENNReal.ofReal (actualConditionalDensity C N p m V U))) :=
    ENNReal.measurable_ofReal.comp (density_meas C (p:=p) hC hm)
  rw [next,Kernel.withDensity_apply _ ht,
    Kernel.const_apply]
  rfl

theorem isMarkov (hC : C.Makes) (hm : m < N) : IsMarkovKernel (next C N p m) :=
  ⟨fun V=>by rw [held C hC hm];exact ActualWilsonConditionalRoots.probability C hC hm V⟩

theorem marginal (hC : C.Makes) (hm : m < N) : next C N p m ∘ₘ (μ m)=μ (m+1) := by
  haveI : IsProbabilityMeasure (μ (m+1)) := OPE.Therm.probability (H:=C.path) (p:=p) hC.wilson hm
  ext S hS
  have h := transfer C (p:=p) hC hm S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
  calc
    _ = ∫⁻ V,ENNReal.ofReal ((fibre C (N:=N) V).real S) ∂μ m := by
      apply lintegral_congr
      intro V
      letI := ActualWilsonConditionalRoots.probability C hC hm V
      rw [held C hC hm,ofReal_measureReal]
    _ = ENNReal.ofReal ((μ (m+1)).real S) := by
      rw [←ofReal_integral_eq_lintegral_ofReal h.1 (ae_of_all _ fun _=>measureReal_nonneg),h.2]
    _ = _ := ofReal_measureReal

def hop (hC : C.Makes) (N p k : ℕ) :
    {K : Kernel (Config G (C.side k p)) (Config G (C.side (k+1) p)) // IsMarkovKernel K} :=
  if h : k < N then ⟨next C N p k,isMarkov C hC h⟩ else ⟨Kernel.const _ (prior G _),inferInstance⟩

def steps (hC : C.Makes) (N p k : ℕ) :
    Kernel ((i : Finset.Iic k) → Config G (C.side i.val p)) (Config G (C.side (k+1) p)) :=
  (hop C hC N p k).val.comap (fun y=>y ⟨k,Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance steps_markov (hC : C.Makes) (N p k : ℕ) : IsMarkovKernel (steps C hC N p k) := by
  letI := (hop C hC N p k).property
  unfold steps
  infer_instance

def path (hC : C.Makes) (N p : ℕ) : Measure ((k : ℕ) → Config G (C.side k p)) :=
  Kernel.trajMeasure (scene C.path N p 0) (steps C hC N p)

instance path_probability (hC : C.Makes) (N p : ℕ) : IsProbabilityMeasure (path C hC N p) := by
  letI : IsProbabilityMeasure (scene C.path N p 0) := OPE.Therm.probability (H:=C.path) (p:=p) hC.wilson (Nat.zero_le N)
  unfold path
  infer_instance

end YM.Integration.QLocalPhysicalPathKernel
end


import YM.Integration.WilsonSeparatedOriginalSlabWatchRoom
import YM.Integration.WilsonSeparatedOriginalSlabWatchDensity

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchMass
open Set Function Filter MeasureTheory RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabWatchRoom WilsonSeparatedOriginalSlabWatchMean WilsonSeparatedOriginalSlabWatchDensity
open scoped Topology ContDiff Classical
variable {I:Type}[Fintype I]

def plot (A:Set (Cloud I)):Set (Points (Fintype.card I)):=ordered '' space A

theorem compact {A:Set (Cloud I)}(closed:IsCompact A):IsCompact (plot A):=(WilsonSeparatedOriginalSlabWatchRoom.compact closed).image seq_continuous

theorem inside {A:Set (Cloud I)}{y:Points (Fintype.card I)}:y∈plot A↔native y∈space A:=by
  constructor
  · rintro ⟨x,h,rfl⟩;simpa only [native_ordered] using h
  · intro h;exact ⟨native y,h,ordered_native y⟩

theorem charged (A:Set (Cloud I))(closed:IsCompact A)(s:I→ℕ)(Ψ:Wave I)(enclosed:tsupport Ψ.val⊆A):
    ∃X:ℝ,0<X ∧ ∀θ:ℝ,θ∈Icc (0:ℝ) 1→∀g:Body,
      Integrable (fun y:Points (Fintype.card I)=>‖(wave θ Ψ g).val (native y)‖) volume ∧
      ∫y:Points (Fintype.card I),‖(wave θ Ψ g).val (native y)‖ ≤volume.real (plot A)*(charge g*X):=by
  have hs:HasCompactSupport Ψ.val:=closed.of_isClosed_subset (isClosed_tsupport _) enclosed
  obtain ⟨X,Xp,sold⟩:=financed s Ψ hs
  refine ⟨X,Xp,?_⟩;intro θ young g
  let b:=fun y:Points (Fintype.card I)=>‖(wave θ Ψ g).val (native y)‖
  have hb:Continuous b:=((show ContDiff ℝ ∞ (wave θ Ψ g).val from (wave θ Ψ g).property).continuous.comp native_continuous).norm
  have cap:IsCompact (plot A):=compact closed
  have estate:tsupport b⊆plot A:=by
    apply closure_minimal _ cap.isClosed;intro y active;apply inside.mpr
    apply WilsonSeparatedOriginalSlabWatchRoom.original θ young Ψ g A closed enclosed
    apply subset_tsupport;intro null;apply active;change ‖(wave θ Ψ g).val (native y)‖=0;rw [null,norm_zero]
  have gross:Integrable b volume:=hb.integrable_of_hasCompactSupport (cap.of_isClosed_subset (isClosed_tsupport _) estate)
  refine ⟨gross,?_⟩
  have each(y:Points (Fintype.card I)):b y≤charge g*X:=by
    simpa only [b,norm_iteratedFDeriv_zero,one_pow,one_mul] using sold θ g 0 (Nat.zero_le _) (native y)
  change ∫y,b y≤_
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (fun y h=>image_eq_zero_of_notMem_tsupport (fun hy=>h (estate hy)))]
  calc ∫y in plot A,b y≤∫_y in plot A,charge g*X:=by
         apply integral_mono (gross.integrableOn) (integrableOn_const (hs:=cap.measure_lt_top.ne));exact each
       _=volume.real (plot A)*(charge g*X):=by rw [setIntegral_const,smul_eq_mul]

end YM.Integration.WilsonSeparatedOriginalSlabWatchMass

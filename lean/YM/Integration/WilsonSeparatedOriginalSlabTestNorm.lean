import YM.Integration.WilsonSeparatedOriginalProfileTest

/-! A compact separated support and one Euclidean distribution order
fund the same smooth-wave estimates for every cutoff test on that compact. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabTestNorm
open Function Filter Set Finset MeasureTheory Lattice Wilson
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Nuclear RG05Readout.Pulse
open RG17 WilsonSeparatedOriginalProfileTest
open scoped Classical BigOperators Topology

def flatten : Cloud (Fin 3) →L[ℝ] Points 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 3=>E4)).symm.toContinuousLinearMap

def scale (M:ℕ):ℝ:=(max 1 ‖flatten‖)^M

def Tested (K:Set (Points 3))(M:ℕ)(X:ℝ)(φ:YM.Test 3):Prop:=
  tsupport (φ:Points 3→ℂ) ⊆ K ∧ ∀j≤M,∀x∈K,‖iteratedFDeriv ℝ j (φ:Points 3→ℂ) x‖ ≤ X

theorem jets {K:Set (Points 3)}{M:ℕ}{X:ℝ}(xp:0 ≤ X)(φ:YM.Test 3)(fit:Tested K M X φ):
    Tall (wave φ) M 1 (scale M*X):=by
  intro j age x
  change ‖iteratedFDeriv ℝ j ((φ:Points 3→ℂ) ∘ (flatten:Cloud (Fin 3)→Points 3)) x‖ ≤ _
  rw [flatten.iteratedFDeriv_comp_right φ.contDiff x (i:=j) (by exact_mod_cast le_top)]
  have bounded:‖iteratedFDeriv ℝ j (φ:Points 3→ℂ) (flatten x)‖ ≤ X:=by
    by_cases h:flatten x∈K
    · exact fit.2 j age _ h
    · rw [notMem_support.mp (fun live=>h (fit.1 (support_iteratedFDeriv_subset j live))),norm_zero]
      exact xp
  have rad:‖flatten‖^j ≤ scale M:=(pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 _) j).trans
    (pow_le_pow_right₀ (le_max_left ..) age)
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,one_pow,one_mul]
  simpa only [mul_comm X] using mul_le_mul bounded rad (pow_nonneg (norm_nonneg _) _) xp

theorem compact {K:Set (Points 3)}(compact:IsCompact K)(separated:K ⊆ conf 3):
    ∃η cap:ℝ,0<η ∧ η ≤ 1 ∧ 0 ≤ cap ∧ ∀(φ:YM.Test 3),tsupport (φ:Points 3→ℂ) ⊆ K →
      Scattering (wave φ) η ∧ ∀y∈tsupport (wave φ).val,∀i:Fin 3,‖y i‖ ≤ cap:=by
  obtain ⟨cap,sep,cp,ep,room⟩:=RG17.roomCosts compact separated
  refine ⟨min sep 1,cap,lt_min ep zero_lt_one,min_le_right ..,cp,?_⟩
  intro φ support
  let c:=PiLp.homeomorph 2 (fun _:Fin 3=>E4)
  have inside:tsupport (wave φ).val ⊆ (WithLp.toLp 2) ⁻¹' tsupport (φ:Points 3→ℂ):=
    closure_minimal (fun _ h=>subset_closure h) ((isClosed_tsupport _).preimage c.symm.continuous)
  constructor
  · intro y hy i j diff
    exact (min_le_left ..).trans (by simpa only [RG17.posed,one_smul,mul_one] using (room 1 one_pos _ (support (inside hy))).spaced i j diff)
  · intro y hy i
    simpa only [RG17.posed,one_smul,sub_zero,mul_one] using (room 1 one_pos _ (support (inside hy))).span i

end YM.Integration.WilsonSeparatedOriginalSlabTestNorm

import YM.Integration.FVA1Physical.Round2.AdjacentReset

/-! The adjacent reset commutes with summing a finite catalogue of
independently generated Wilson rows. Every row uses one measured coupling
jet and its inverse field rescaling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Filter Finset Lattice RG MSbar MSbar.Rolling MSbar.Bakery MSbar.Cacao MSbar.Wave
open MSbar.Bakery.Portal Comparison.RG02 PertExtension.Series PertExtension.Series.Tested
open scoped BigOperators Classical ContDiff Topology
variable {σ ι : Type} [Fintype σ]

theorem reset_catalogue {H : ℝ → ℝ} {b : PowerSeries ℝ} (s : Finset ι)
    (V : ι → PowerSeries (Pot σ)) (r : ℕ) (h₀ : H 0 = 1) (hb : PowerSeries.coeff 0 b = 1)
    (hs : ContDiffAt ℝ ω H 0) (hH : Approx H b r) (deg : ∀ j ∈ s, Expanse (V j) 1 r)
    (x : View σ) {i : ℕ} (hi : i ≤ r) :
    Adjacent.born (fun k y=>∑ j∈s, displayed (V j) k y) (sceneGerm H hs h₀) 0 r i x =
      ∑ j∈s, displayed (ticket b (V j)) i x := by
  let K := sceneGerm H hs h₀
  let rowRead (j : ι) (t : ℝ) := Adjacent.ages (displayed (V j)) 0 r t (K.rating t) x
  have eqj (j : ι) : rowRead j = Complex.ofRealCLM ∘ transportedRead H (V j) r x := by
    funext t
    simp [rowRead,K,Adjacent.ages,Adjacent.cover,sceneGerm,displayed,transportedRead,taste,picture,div_eq_mul_inv]
  have hj (j : ι) : ContDiffAt ℝ ω (rowRead j) 0 := by
    rw [eqj]
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0
      (transportedRead_smooth (V j) r x hs (h₀.trans_ne one_ne_zero))
  have eqs : (fun t=>Adjacent.ages (fun k y=>∑ j∈s,displayed (V j) k y) 0 r t (K.rating t) x) =
      (fun t=>∑ j∈s, rowRead j t) := by
    funext t
    simp only [rowRead,Adjacent.ages,Adjacent.cover,zpow_zero,Complex.ofReal_one,one_mul,mul_sum]
    exact sum_comm
  change Moving.Path.motion _ i = _
  rw [eqs,Moving.Shift.msum _ _ (fun j _=>hj j)]
  exact sum_congr rfl fun j h => ticket_adjacent (V j) r h₀ hb hs hH (deg j h) x hi
end YM.Integration.FVA1Physical.Round2

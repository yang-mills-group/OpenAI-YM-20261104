import YM.FVA2.OffsetClock

/-! The primitive clock-dependent account of the measured nonlinear history
has exactly the Taylor coefficients of the independent FVA2 exponent. The
clock series may have linear, quadratic or higher corrections at every tier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Lattice RG Tree RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial
open PertExtension.Series.Tested FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MultiGauge
open FormalOPE.RG10.MultiGauge.Stack FVA2.CityHistory FVA2.CityHistory.Legacy
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side}

private theorem value_prod {f g : ℝ → ℝ} {A B : PowerSeries ℝ}
    (hf : Aspiration f (term A)) (hg : Aspiration g (term B)) :
    Aspiration (f*g) (term (A*B)) := by
  have back (A : PowerSeries ℝ) : PowerSeries.mk (term A) = A :=
    PowerSeries.ext (fun i => PowerSeries.coeff_mk ..)
  simpa only [conv,back] using hf.prod hg

private theorem value_add {f g : ℝ → ℝ} {A B : PowerSeries ℝ}
    (hf : Aspiration f (term A)) (hg : Aspiration g (term B)) :
    Aspiration (f+g) (term (A+B)) := by
  rw [show term (A+B) = term A + term B from funext fun i => map_add _ _ _]
  exact hf.add hg

private theorem radial_value {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (h : ContDiffAt ℝ ω f 0) (x : E) :
    Aspiration (fun g : ℝ => f (g • x)) (term (read x (rise f))) := by
  rw [show term (read x (rise f)) = fun i => jet f i x from funext (read_rise x f)]
  exact directions (h.of_le le_top) x

theorem actual_account_coefficients (d : Descent n c) (t : d.Tags) (h : d.OK G)
    (z : ℕ → ℝ → ℝ) (w : ℕ → PowerSeries ℝ)
    (hz : ∀ i ≤ d.depth, Aspiration (z i) (term (w i))) (v : SpaceF G d) :
    Aspiration (fun g : ℝ => consume d t (fun i => z i g) (g • v))
      (term (read v (moneyX d t w))) := by
  induction d generalizing z w with
  | nil =>
    rw [moneyX,caught,map_mul,load]
    exact value_prod (hz 0 le_rfl) (radial_value (born_hot G n) v.2)
  | @push c f S T d ih =>
    rcases t with ⟨b,t⟩
    rw [moneyX,map_add,caught,caught,map_mul,load]
    have eqn (g : ℝ) := at_step S T d t b (fun i => z i g) (g • v)
    simp only [map_smul] at eqn
    simp_rw [eqn]
    apply value_add
    · exact ih t h.2 (fun i => z (i+1)) (parentZ w)
        (fun i hi => hz (i+1) (Nat.succ_le_succ hi)) _
    exact value_prod (hz 1 (Nat.succ_le_succ (Nat.zero_le _))) (radial_value (tax_hot S T b h.1) _)

end YM.Integration.FVA1Physical.Wilson

import YM.Integration.FVA1Physical.Wilson.SparsePhysical
import YM.Integration.FVA1Physical.Wilson.CroppedMean
import YM.Next.FLUCTUATIONS.Charts

/-! A k-bond chart prices invariant observables on the original physical field.
Bonds can be placed independently at any distances. Outside the sampled
gauge window a bounded physical insertion pays only the physical exception. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set MeasureTheory Finset Lattice RG YM.Wilson Pressure MSbar.Heath.Cottage MSbar.Heath.Stock
open OPE.Therm Qlocal.Schedule YM.Integration.FVA1Physical.Round2.Curvature
open PhysicalNext.Repeat Next.Fluctuations Push.Uniform Precision MSbar.Rolling MSbar.Midpoint
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}

def bondMask (B : Finset (Edge (Site n))) (U : Config G n) : Config G n :=
  fun e => if e∈B then U e else 1

theorem bondMask_cont (B : Finset (Edge (Site n))) : Continuous (bondMask (G:=G) B) := by
  apply continuous_pi
  intro e
  unfold bondMask
  split <;> fun_prop

theorem bond_chart (G : Gauge) : ∃ C δ : ℝ, 0<C ∧ 0<δ ∧
    ∀ {n : Side} (B : Finset (Edge (Site n))) {τ : ℝ}, 0≤τ → τ≤δ →
    ∀ U∈edgeWindow (G:=G) B τ, ∃ z : Positions (Primary n G),
      ‖z‖≤C*τ ∧ Boulevard.actual z = bondMask B U := by
  obtain ⟨C,δ,hC,hδ,chart⟩ := extend_interior G
  refine ⟨C,δ,hC,hδ,?_⟩
  intro n B τ non small U hit
  let W := bondMask B U
  have bound (e : Edge (Site n)) : G.chord (W e) ≤ τ := by
    by_cases he:e∈B
    · simpa only [W,bondMask,if_pos he] using (hit e he).le
    · simpa only [W,bondMask,if_neg he,G.chord_one] using non
  obtain ⟨b,hb,agrees⟩ := chart (fun _=> (0:Site n)) 0 0 W τ non small (fun e _=>bound e)
  refine ⟨(tint G _).symm b,(tint_inv_le _).trans hb,?_⟩
  unfold Boulevard.actual
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact funext fun e => (agrees e (by simp)).symm

/-- Local analytic control in a common normalized edge window transfers to
the physical law before any cutoff, ambient period or marker sites are fixed. -/
theorem sparse_observable_mean (R : PhysicalNext.Repeat.Legato.Run G) (simple : G.Simple)
    (gate : selectedThreshold (angularThreshold G) R.metals R.rolls R.alloy R.kit) (k K : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (N n : ℕ) (_ : j+1≤N) (B : Finset (Edge (Site (R.family.side (j+1) n)))) (_ : B.card≤k)
      (P Q : Config G (R.family.side (j+1) n) → ℝ) (e cap : ℝ), 0≤e → 0≤cap →
      GaugeInvariant P → Measurable P → Measurable Q → (∀U,|P U|≤cap) →
      let x:=R.family.path.levels.clock.hatBeta (j+1);let win:=edgeWindow (G:=G) B (room x)
      (∀U∈win, |P U-Q U|≤e) →
      (∫ U, |P U-orbitWindow win Q U| ∂(scene R.family.path N n (j+1))) ≤
        e+(sparseCount k:ℝ)*(x⁻¹)^K*cap := by
  filter_upwards [sparse_physical R simple gate k K] with j paid N n hj B count P Q e cap ep cp sym pm qm hcap x win chart
  let μ:=scene R.family.path N n (j+1)
  haveI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=n) R.T.choice hj
  have hopen:IsOpen win:=edgeWindow_open B _
  obtain ⟨rare,rpos,_,entry⟩:=paid N n hj B count
  have mass : μ.real {U:Config G (R.family.side (j+1) n)|∃ z:Site (R.family.side (j+1) n)→G.El,Lattice.gauge z U ∈win}ᶜ
       ≤ (sparseCount k:ℝ)*(x⁻¹)^K := by
    apply (measureReal_mono (μ:=μ) ?_).trans rare
    intro U miss good
    obtain ⟨z,fine⟩:=entry U good
    apply miss
    exact ⟨z,fun e he=>by have h:=fine e he;linarith only [h,rpos]⟩
  have bound:=cropped_orbit_mean μ id continuous_id win hopen P Q pm qm e cap ep cp
    (fun V a ha=>orbitWindow_price win hopen P Q sym qm V a ha chart) hcap
  exact bound.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right mass cp))

end YM.Integration.FVA1Physical.Wilson

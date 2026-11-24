import YM.Integration.WilsonMatrixOriginalEarlierPanel
import YM.Integration.WilsonMatrixOriginalPanelInverse

/-! Decode the earlier regular Gibbs covariance using the measured upper Wilson covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalCapturedInverse
open Filter Function Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order Table Spec Climb
open Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonInvariantActionCalibratedColumn WilsonInvariantActionPosition WilsonMatrixOriginalFiledPanel
open WilsonInvariantActionCapturedProfile
open scoped Classical Topology BigOperators

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

/-- Homogeneity holds in the submitted test of the complete earlier two-field covariance. -/
theorem sample (R : Run G) {k N per : ℕ} (live : k ≤ N) (marks : Fin 2 → R.family.label 4)
    {r : ℝ} (hr : 0 < r) (φ : Test 2) (t : ℂ) :
    earlier R (per:=per) live marks (dilate hr (t • φ)) =
      t * earlier R (per:=per) live marks (dilate hr φ) := by
  have point (x : Points 2) : dilate hr (t • φ) x = t * dilate hr φ x := by
    change (((r^(4*2))⁻¹ : ℝ) : ℂ) * (t * φ (r⁻¹ • x)) =
      t * ((((r^(4*2))⁻¹ : ℝ) : ℂ) * φ (r⁻¹ • x))
    ring
  unfold earlier
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [WilsonExternalMeshMass.charge,point]
  ring

variable (F : Final R.family f S) (L : Layout F) {U : Filter (ℕ × ℕ)}

def Recovered (g : ℝ → ℝ) (a b : ℝ → R.family.label 4) (χ : ℂ →L[ℝ] ℝ) (σ : ℝ)
    (φ : Test 2) (c : ℂ) : Prop :=
  let K := 4 / |χ c|
  0 < K ∧ ∀ q : ℕ, ∀ ε > 0, ∀ᶠ r in trail,
    let k := berth R (q+28) (L.level r)
    ∀ hr : 0 < r, ∀ᶠ z : ℕ × ℕ in U, ∃ live : k < z.1,
      let marks := Fin.cons (α:=fun _ : Fin 2 => R.family.label 4) (atRef L 4 r z (a r))
        (fun _ => atRef L 4 r z (b r))
      let d := (σ * Value F L a b χ φ hr z)⁻¹
      let high := fun (t : ℝ) => σ * Value F L a b χ ((t:ℂ) • φ) hr z
      let low := fun (t : ℝ) => σ * χ (earlier R (per:=z.2) live.le marks (dilate hr ((t:ℂ) • φ)))
      0 < d ∧ d < K ∧ (∀ t : ℝ, d * high t = t) ∧
        ∀ t noise : ℝ, |d * (low t + noise) - t| ≤ ε*(g r)^q*|t| + K*|noise|

private theorem noisy {d σ high low t noise K price allowance : ℝ}
    (hp : 0 ≤ d) (cap : d ≤ K) (sgn : |σ| = 1) (inv : d * (σ*high) = 1)
    (near : |high-low| ≤ price) (cost : d*price ≤ allowance) :
    |d*(σ*(t*low)+noise)-t| ≤ allowance*|t| + K*|noise| := by
  have identity : d*(σ*(t*low)+noise)-t = d*(σ*(low-high))*t + d*noise := calc
    _ = d*(σ*(t*low)+noise) - (d*(σ*high))*t := by rw [inv,one_mul]
    _ = _ := by ring
  rw [identity]
  apply (abs_add_le ..).trans
  apply add_le_add
  · simp only [abs_mul,abs_of_nonneg hp,sgn,one_mul]
    rw [abs_sub_comm low high]
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left near hp).trans cost) (abs_nonneg t)
  · simpa only [abs_mul,abs_of_nonneg hp] using mul_le_mul_of_nonneg_right cap (abs_nonneg noise)

/-- The row's filed orientation and its empirical upper denominator decode every earlier amplitude. -/
theorem on_row (J : ℝ → tower S) (Z : WilsonPrescription G) {H : (Bel R.family.book).Hierarchy}
    {δ g : ℝ → ℝ} {D : Profiles R 4} {j : D.probes.index} {w : (standard R.family.labels).Ref 4}
    {hs : D.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w}
    {e : ℕ} {deposit : ℝ → RG17.Free R.family 4 → R.family.label 4} {χ : ℂ →L[ℝ] ℝ} {σ : ℝ}
    (row : WilsonMatrixOriginalEarlierPanel.Row (H:=H) (U:=U) F J Z L δ g D j w hs e deposit χ σ) :
    Recovered (U:=U) F L g (fun r => deposit r (stepField R.family))
      (fun r => deposit r (freeInput F J Z 4 r ((Bel R.family.book).project 4 w))) χ σ
      (packet w hs (test D j)) (tree (D.probes.shell j) (test D j) H 4 (stepField R.family)) := by
  let φ := packet w hs (test D j)
  let v := (Bel R.family.book).project 4 w
  let a := fun r => deposit r (stepField R.family)
  let b := fun r => deposit r (freeInput F J Z 4 r v)
  let c := tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
  let cov := fun r => tested (J r 4 (stepField R.family)) (homogeneous F J Z r 4 v) r φ
  let K := 4 / |χ c|
  obtain ⟨_,sign,orient,nz,limit,_,filed,_,stages⟩ := row
  have sg : |σ| = 1 := by rcases sign with rfl | rfl <;> norm_num
  have kp : 0 < K := div_pos (by norm_num) nz
  have signedLimit : Tendsto (fun r => σ * χ (cov r)) trail (𝓝 |χ c|) := by
    rw [←orient]
    exact tendsto_const_nhds.mul ((χ.continuous.tendsto _).comp limit)
  have gap := signedLimit.eventually (lt_mem_nhds (show |χ c|/2 < |χ c| by linarith))
  change Recovered (U:=U) F L g a b χ σ φ c
  refine ⟨kp,?_⟩
  intro q ε ep
  let η := ε/K
  have affordable : 0 < η := div_pos ep kp
  have exchange : K*η = ε := by dsimp only [η]; field_simp
  have saved := stages q η affordable
  simp only [show 2*1+q+1+25=q+28 by omega] at saved
  filter_upwards [gap,filed.2,saved] with r margin convergence price
  intro k hr
  have reads : Tendsto (fun z => σ * Value F L a b χ φ hr z) U (𝓝 (σ * χ (cov r))) :=
    tendsto_const_nhds.mul (convergence hr).2.1
  have highEnough := reads.eventually (lt_mem_nhds ((show |χ c|/4 < |χ c|/2 by linarith).trans margin))
  filter_upwards [highEnough,price hr] with z large purchased
  obtain ⟨live,_,_,_,close⟩ := purchased
  let marks := Fin.cons (α:=fun _ : Fin 2 => R.family.label 4) (atRef L 4 r z (a r))
    (fun _ => atRef L 4 r z (b r))
  let low := χ (earlier R (per:=z.2) live.le marks (dilate hr φ))
  let high := Value F L a b χ φ hr z
  let d := (σ*high)⁻¹
  have strong : |χ c|/4 < σ*high := large
  have nonzero : 0 < σ*high := (div_pos nz (by norm_num)).trans strong
  have dp : 0 < d := inv_pos.mpr nonzero
  have cap : d < K := by
    change (σ*high)⁻¹ < 4/|χ c|
    rw [inv_eq_one_div,div_lt_div_iff₀ nonzero nz]
    linarith
  have inv : d*(σ*high) = 1 := inv_mul_cancel₀ nonzero.ne'
  have exactSignal (t : ℝ) : d*(σ*Value F L a b χ ((t:ℂ) • φ) hr z) = t := by
    rw [WilsonMatrixOriginalPanelInverse.sample]
    calc
      _ = (d*(σ*high))*t := by dsimp only [high]; ring
      _ = t := by rw [inv,one_mul]
  have near : |high-low| ≤ η*(g r)^q := close
  have paid : d*(η*(g r)^q) ≤ ε*(g r)^q := calc
    _ ≤ K*(η*(g r)^q) := mul_le_mul_of_nonneg_right cap.le ((abs_nonneg _).trans near)
    _ = _ := by rw [←mul_assoc,exchange]
  refine ⟨live,dp,cap,exactSignal,?_⟩
  intro t noise
  change |d*(σ*χ (earlier R (per:=z.2) live.le marks (dilate hr ((t:ℂ) • φ)))+noise)-t| ≤ _
  rw [sample R,show χ ((t:ℂ) * earlier R (per:=z.2) live.le marks (dilate hr φ)) = t*low from χ.map_smul t _]
  exact noisy dp.le cap.le sg inv near paid

end YM.Integration.WilsonMatrixOriginalCapturedInverse
end

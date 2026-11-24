import YM.Integration.FVA1Physical.Round2.VacuumJetTail
import YM.Integration.FVA1Physical.Round2.VacuumExpansion
import YM.Integration.FVA1Physical.Round2.PurchasedVacuum

/-! Localize the weighted regular derivative rows of the actual calibrated
vacuum discrepancy on the same scene that furnishes its coupling reset. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open Filter RG Wilson Precision MSbar.Midpoint PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology
variable {σ : Type} [Fintype σ] {n : Side}

/-- All held derivative addresses and all distant fields may vary. -/
theorem rooted_jet_near {site : σ → Site n} {a w B : ℝ} {s k q : ℕ}
    {F : Positions σ → ℝ} (J : JetTab site a s w (Metric.closedBall 0 w) F (q+1) B)
    (hw : 0 < w) (ha : 0 ≤ a) (hf : ∀ x ∈ Metric.closedBall 0 w, ContDiffAt ℝ k F x)
    (hk : q+2 ≤ k) (i : σ) (r : ℕ) {x : Positions σ} (hx : x ∈ Metric.closedBall 0 w) :
    Yarn q (fun l : List σ =>
      |buoy F x (i::l) - buoy F (nearField site i r x) (i::l)| *
        Measuring.swipe site (a/2) s (i::l)) ≤ B / w^(q+1) / liftW (a/2) 0 (r+1) := by
  let y := nearField site i r x
  let v := x-y
  have hy : y ∈ Metric.closedBall 0 w :=
    mem_closedBall_zero_iff.mpr ((nearField_norm ..).trans (mem_closedBall_zero_iff.mp hx))
  have hv : ‖v‖ ≤ w := by
    refine le_trans ((pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_) (mem_closedBall_zero_iff.mp hx)
    intro j
    by_cases h : separation (site i) (site j) ≤ r
    · simp [v,y,nearField,h]
    · simpa [v,y,nearField,h] using norm_le_pi_norm x j
  have far (j : σ) (hj : v j ≠ 0) : r+1 ≤ separation (site i) (site j) := by
    by_contra! e
    have he : separation (site i) (site j) ≤ r := by omega
    simp [v,y,nearField,he] at hj
  have stay (t : ℝ) (ht : t ∈ Set.Icc 0 1) : y+t • v ∈ Metric.closedBall 0 w := by
    have cv := (convex_closedBall (0 : Positions σ) w) hy hx (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    convert cv using 1
    dsimp only [v]; rw [smul_sub,sub_smul,one_smul]; abel
  have h := rooted_jet_tail J hw ha hf hk i (r+1) y v stay far
  rw [show y+v=x by dsimp [v]; abel] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (wpos ..).le)
  calc
    ‖v‖/w^(q+2)*B ≤ w/w^(q+2)*B :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hv (pow_nonneg hw.le _)) J.zeroP
    _ = _ := by rw [show q+2=(q+1)+1 by omega,pow_succ]; field_simp

/-- A Docket pays the scalar, all localized regular derivative rows, and
the next physical coupling on the identical scene, on every admitted torus.
The number of derivative directions and changed sites does not enter the price. -/
theorem calibrated_jet_shells {G : Gauge} {C : Family G} {Z : Horizon C.path.levels}
    {u : G.ColorIndex} {O : ChartRatio G} {K : Kin Z O} (hG : G.Simple)
    (D : Docket C u O Z K)
    (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m) (hp : p+2 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ (N i : ℕ), k ≤ N → ∃ S : Scene C.path.levels i p,
      Realized K N i k p (Lis.sun G u) S ∧
      (∀ j, k ≤ j → j ≤ N →
        let Q := C.path.rep N i j
        let β := C.path.levels.clock.hatBeta j
        let w := Mosaic.vol β
        let a := Mosaic.αm β
        let site := Measuring.chart (C.path.levels.S.side j i) G
        let F := Aqua.film Q (S.Poly j) (Heath.Stock.cue Q.beta) p
        ∀ x ∈ Metric.closedBall 0 w,
          F x = F 0 + ∑ v, ∑ r ∈ Finset.range (extent (Finset.univ.image site)+1), radialShell site F v x r ∧
          ∀ (q : ℕ), q+2 ≤ m → ∀ v r, Yarn q (fun l =>
            |buoy F x (v::l)-buoy F (nearField site v r x) (v::l)| *
              Measuring.swipe site (a/2) s (v::l)) ≤ (5*Mosaic.goalP β p)/w^(q+1)/liftW (a/2) 0 (r+1)) ∧
      ∀ j, k ≤ j → j < N →
        |Heath.Stock.cue (C.path.rep N i j).beta / Heath.Stock.cue (C.path.rep N i (j+1)).beta -
          Bakery.taste p (S.action j) (Heath.Stock.cue (C.path.rep N i j).beta)| ≤
          Mosaic.goalP (C.path.levels.clock.hatBeta j) p := by
  have grows := Alto.broad.comp (Multi.Wage.hat_tend hG C.path.levels)
  obtain ⟨k₀,h₀⟩ := Filter.eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [D.purse s p m hs hm hp,eventually_ge_atTop k₀] with k paid hk
  intro N i hkN
  obtain ⟨⟨S,hS⟩,covers⟩ := paid N i hkN
  obtain ⟨tickets,reset,_⟩ := covers S hS
  refine ⟨S,hS,?_,reset⟩
  intro j hkj hjN
  dsimp only
  intro x hx
  have T := tickets j hkj hjN
  have wide := h₀ j (hk.trans hkj)
  have hw : 0 < Mosaic.vol (C.path.levels.clock.hatBeta j) := div_pos wide (by norm_num)
  have ha : 0 ≤ Mosaic.αm (C.path.levels.clock.hatBeta j) := zpow_nonneg wide.le _
  refine ⟨shells_reconstruct T.grown (by omega) hx,?_⟩
  intro q hq v r
  have J := JetTab.levelAll hw ha T.grown T.rangeP hm le_rfl (q+1) (by omega)
  exact rooted_jet_near J hw ha T.grown (by omega) v r hx

end YM.Integration.FVA1Physical.Round2

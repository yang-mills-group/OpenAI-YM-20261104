import YM.Integration.FVA1Physical.Wilson.BoundaryRows

/-! Oscillation of the discrepancy between the physical incoming action and the independently
iterated Wilson action on a finite patch. Exterior links can be arbitrarily nonflat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16 Pressure
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {σ : Type} [Fintype σ] {c : Side}

theorem patch_oscillation {site : σ→Site c} {a w B : ℝ} {s : ℕ} {S : Set (Positions σ)}
    {F : Positions σ→ℝ} (J : JetTab site a s w S F 0 B) (hw : 0<w) (ha : 0 ≤ a)
    (smooth : ∀ y∈S, DifferentiableAt ℝ F y) (x v : Positions σ)
    (inside : ∀ t ∈ Set.Icc (0:ℝ) 1, x+t • v ∈ S) :
    |F (x+v) - F x| ≤ (∑ i, |v i|) * (B/w) := by
  have entry (y : Positions σ) (hy : y∈S) (i : σ) : |fderiv ℝ F y (bolt i)| ≤ B/w := by
    have h := J.count hw y hy i
    change |fderiv ℝ F y (bolt i)| * Measuring.swipe site a s [i] ≤ B/w^(0+1) at h
    have weight : 1 ≤ Measuring.swipe site a s [i] := w_start ha s _
    exact (le_mul_of_one_le_right (abs_nonneg _) weight).trans (by simpa only [zero_add,pow_one] using h)
  have price (y : Positions σ) (hy : y∈S) : ‖fderiv ℝ F y v‖ ≤ (∑ i, |v i|) * (B/w) := by
    nth_rw 1 [spiral v]
    rw [map_sum,Finset.sum_mul]
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro i _
    rw [map_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (entry y hy i) (abs_nonneg _)
  have H (t : ℝ) (ht : t∈Set.Icc 0 1) :
      HasDerivAt (fun t : ℝ=> F (x+t • v)) (fderiv ℝ F (x+t • v) v) t := by
    apply (smooth _ (inside t ht)).hasFDerivAt.comp_hasDerivAt
    simpa using ((hasDerivAt_id' t).smul_const v).const_add x
  have P := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f:=fun t : ℝ=>F (x+t • v)) (f':=fun t=>fderiv ℝ F (x+t • v) v)
    (fun t ht=>(H t ht).hasDerivWithinAt) (fun t ht=>price _ (inside t (Set.Ico_subset_Icc_self ht)))
  simpa only [one_smul,zero_smul,add_zero,Real.norm_eq_abs] using P

variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path)

/-- The physical and independently rebuilt Wilson weights have a volume-independent
relative log price on every bounded-displacement incoming chart, at every RG depth. -/
theorem uniform_patch_oscillation (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj : j ≤ N, ∀ (T : Slices C.path.levels n)
        (h : (traversal T hj).Room G) (tag : (traversal T hj).Tags)
        (x v : Positions (Primary (C.side j n) G)),
        let g := Heath.Stock.cue (C.path.rep N n j).beta
        let w := Mosaic.vol (C.path.levels.clock.hatBeta j)
        let E := sceneVacuumError L S T hj h tag p g
        (∀ t ∈ Set.Icc (0:ℝ) 1, x+t • v ∈ Metric.closedBall 0 w) →
        |E (x+v)-E x| ≤ (∑ i, |v i|) * (g^((p:ℝ)+1-η)/w) := by
  have grows := Alto.broad.comp (Multi.Wage.hat_tend simple C.path.levels)
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [uniform_ledger_envelope L u simple sel D s p m 0 hs hm hp (by omega) hη,
    D.purse s (p+1) m hs hm hp,eventually_ge_atTop k₀] with k bought purse cutoff
  intro N n lo
  obtain ⟨S,hS,rows,_⟩ := bought N n lo
  have checks := ((purse N n lo).2 S hS).1
  refine ⟨S,hS,?_⟩
  intro j hk hj T h tag x v g w E inside
  let Q := C.path.rep N n j
  have wide := h₀ j (cutoff.trans hk)
  apply patch_oscillation (rows j hk hj T h tag) (div_pos wide (by norm_num))
    (zpow_nonneg wide.le _) _ x v inside
  intro y hy
  change DifferentiableAt ℝ (sceneVacuumError L S T hj h tag p g) y
  rw [←sceneVacuumError_eq L S T hj h tag hS hk (Nat.le_succ p)]
  have top : ContDiffAt ℝ (2:ℕ) (Aqua.film Q (S.Poly j) g (p+1)) y :=
    ((checks j hk hj).grown y hy).of_le (by exact_mod_cast (show 2 ≤ m+1 by omega))
  have pure (i) := (Aqua.pure Q (S.Poly j) g i).contDiffAt (x:=y)
  have actual : ContDiffAt ℝ (2:ℕ) (Aqua.vine Q g) y := by
    have all := top.add ((pure (p+1)).of_le le_top)
    convert all using 1
    funext z;change Aqua.vine Q g z=(Aqua.vine Q g z-_) + _;abel
  exact (actual.sub ((pure p).of_le le_top)).differentiableAt (by simp)

end YM.Integration.FVA1Physical.Wilson

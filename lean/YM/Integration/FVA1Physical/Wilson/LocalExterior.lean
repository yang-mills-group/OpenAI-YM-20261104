import YM.Integration.FVA1Physical.Wilson.HaarInherited

/-! Insert the independent local vacuum interaction in the full physical transition.
Exterior fields retain their actual anchor weight and are averaged over their true
Haar measure. The error counts only the locally replaced coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {σ : Type} [Fintype σ]

def freeze (I : Finset σ) (x : Positions σ) : Positions σ := fun i => if i∈I then 0 else x i

omit [Fintype σ] in
theorem freeze_cont (I : Finset σ) : Continuous (freeze I) := by
  apply continuous_pi
  intro i
  by_cases h : i∈I
  · simpa only [freeze,if_pos h] using (continuous_const : Continuous (fun _ : Positions σ => (0:ℝ)))
  · simpa only [freeze,if_neg h] using (continuous_apply (A:=fun _:σ=>ℝ) i)

theorem interpolate_freeze {w : ℝ} (I : Finset σ) (z : Positions σ) (hz : ‖z‖ ≤ w) :
    (∑ i, |(z-freeze I z) i|) ≤ I.card*w ∧
    ∀ t∈Set.Icc (0:ℝ) 1, freeze I z+t • (z-freeze I z) ∈ Metric.closedBall 0 w := by
  have hw := (norm_nonneg z).trans hz
  have h (i : σ) : |z i| ≤ w := (pi_norm_le_iff_of_nonneg hw).mp hz i
  constructor
  · rw [←Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [freeze,hi])]
    calc
      ∑ i∈I,|(z-freeze I z) i| ≤ ∑ _i∈I,w := Finset.sum_le_sum fun i hi=>by simpa [freeze,hi] using h i
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  intro t ht
  apply mem_closedBall_zero_iff.mpr
  apply (pi_norm_le_iff_of_nonneg hw).mpr
  intro i
  by_cases hi : i∈I
  · simp only [freeze,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,if_pos hi,sub_zero,zero_add,norm_smul,Real.norm_of_nonneg ht.1]
    exact ((mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (z i))).trans_eq (one_mul _)).trans (h i)
  · simpa only [freeze,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,if_neg hi,sub_self,smul_zero,add_zero,Real.norm_eq_abs] using h i

variable {G : Gauge} {f : Side}
def regularInputs (g w : ℝ) : Set (Config G f) :=
  Set.univ.pi (fun _=>exponentialPatch G) ∩ {U | ‖chartLog g U‖ ≤ w}

theorem regular_meas (g w : ℝ) : MeasurableSet (regularInputs (G:=G) (f:=f) g w) := by
  apply MeasurableSet.inter
  · apply MeasurableSet.univ_pi
    intro e
    exact ((LocalH.geom_patch G).choose_spec.2 _ le_rfl).1.measurableSet
  exact measurableSet_le (chartLog_meas g).norm measurable_const

private theorem measurable_palace : Measurable (palace (G:=G) (c:=f)) := by
  apply Continuous.measurable
  apply continuous_pi
  intro e
  exact (G.lieExp_cont.comp ((continuous_apply e).comp (panel G f).continuous)).mul continuous_const

/-- The physical exterior-anchor log and independently computed interior action
increment on regular fields; the physical action itself on the exceptional sector. -/
def localWilsonLog (I : Finset (Primary f G)) (g w : ℝ) (Q : Config G f→ℝ)
    (B : Positions (Primary f G)→ℝ) : Config G f→ℝ :=
  (regularInputs g w).piecewise (fun U=> let z := chartLog g U
    Real.log (Q (palace (g • freeze I z))) + (B z-B (freeze I z))) (fun U=>Real.log (Q U))

theorem localWilsonLog_meas (I : Finset (Primary f G)) (g w : ℝ) {Q : Config G f→ℝ}
    (hQ : Measurable Q) {B : Positions (Primary f G)→ℝ} (hB : Continuous B) :
    Measurable (localWilsonLog I g w Q B) := by
  have z := chartLog_meas (G:=G) (f:=f) g
  have q := (freeze_cont I).measurable.comp z
  exact ((Real.measurable_log.comp (hQ.comp (measurable_palace.comp (q.const_smul g)))).add
      ((hB.measurable.comp z).sub (hB.measurable.comp q))).piecewise (regular_meas g w) (Real.measurable_log.comp hQ)

/-- A pointwise volume-independent relative log price on the entire physical input,
so the same comparison can be used with its original or any gauge-fixed chart. -/
theorem local_log_estimate {g w ε : ℝ} (hg : g ≠ 0) (hw : 0 < w) (hε : 0 ≤ ε)
    (Q : Config G f→ℝ) (B : Positions (Primary f G)→ℝ) (I : Finset (Primary f G))
    (rows : ∀ x v : Positions (Primary f G),
      (∀ a ∈ Set.Icc (0:ℝ) 1, x+a • v ∈ Metric.closedBall 0 w) →
      |(Real.log (Q (palace (g • (x+v)))) - B (x+v)) - (Real.log (Q (palace (g • x)))-B x)| ≤
        (∑ i, |v i|)*(ε/w)) (U : Config G f) :
    |Real.log (Q U)-localWilsonLog I g w Q B U| ≤ (I.card:ℝ)*ε := by
  let R := fun z : Positions (Primary f G)=> Real.log (Q (palace (g • z)))-B z
  rw [localWilsonLog]
  by_cases good : U∈regularInputs g w
  · rw [Set.piecewise_eq_of_mem _ _ _ good]
    let z := chartLog g U
    let x := freeze I z
    have whole : x + (z-x) = z := by abel
    have hz : ‖z‖ ≤ w := good.2
    obtain ⟨sz,within⟩ := interpolate_freeze I z hz
    have priced := rows x (z-x) within
    rw [whole] at priced
    have eq : Real.log (Q U) - (Real.log (Q (palace (g • x))) + (B z-B x)) = R z-R x := by
      change _ = (Real.log (Q (palace (g • z)))-B z)-(Real.log (Q (palace (g • x)))-B x)
      rw [show palace (g • z) = U from recover_chartLog hg U (Set.mem_univ_pi.mp good.1)]
      ring
    change |Real.log (Q U) - (Real.log (Q (palace (g • x))) + (B z-B x))| ≤ _
    rw [eq]
    exact priced.trans ((mul_le_mul_of_nonneg_right sz (div_nonneg hε hw.le)).trans_eq (by field_simp))
  · rw [Set.piecewise_eq_of_notMem _ _ _ good,sub_self,abs_zero];exact mul_nonneg (Nat.cast_nonneg _) hε

variable {C : Family G} (L : Bulk.Chain C.path) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform in the full retained volume and all exterior configurations. The local
oscillation of the physical incoming action on any finite set of bonds is replaced
by the Wilson action at the measured coupling; the full outer conditional average
is normalized anew and tested by arbitrary bounded mixed observables. -/
theorem averaged_local_replacement (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj : j < N, ∀ (T : Slices C.path.levels n) (h : (traversal T hj).Room G)
        (t : (traversal T hj).Tags) (V : Config G (C.side j n)) (I : Finset (Primary (C.side (j+1) n) G)),
        let Q := C.path.rep N n (j+1)
        let g := Heath.Stock.cue Q.beta
        let w := Mosaic.vol (C.path.levels.clock.hatBeta (j+1))
        let μ := prior G (C.side (j+1) n)
        let K := fun U=>(C.path.levels.clock.op j n).density Q.beta U V
        let B := boundaryBank L S T hj h t p g
        let ξ := (I.card:ℝ)*g^((p:ℝ)+1-η)
        ∀ (F : Config G (C.side (j+1) n)→E), AEStronglyMeasurable F μ →
        ∀ M : ℝ, 0 ≤ M → (∀ᵐ U ∂μ, ‖F U‖ ≤ M) →
        ‖patchMean μ (fun U=>K U * Q.eval U) F - patchMean μ
          (fun U=>K U * Real.exp (localWilsonLog I g w Q.eval B U)) F‖ ≤ (Real.exp (2*ξ)-1)*M := by
  have high := Multi.Wage.hat_tend simple C.path.levels
  obtain ⟨k₁,h₁⟩ := eventually_atTop.mp (high.eventually_gt_atTop 0)
  obtain ⟨k₂,h₂⟩ := eventually_atTop.mp ((Alto.broad.comp high).eventually_gt_atTop 0)
  filter_upwards [uniform_patch_oscillation L u simple sel D s p m hs hm hp hη,eventually_ge_atTop k₁,
    eventually_ge_atTop k₂] with k bought cut₁ cut₂
  intro N n lo
  obtain ⟨S,hS,rows⟩ := bought N n lo
  refine ⟨S,hS,?_⟩
  intro j hk hj T h t V I Q g w μ K B ξ F hF M hM hb
  have hjk := hk.trans (Nat.le_succ j)
  have hβ := (half_pos (h₁ _ (cut₁.trans hjk))).trans_le (sel.represents N n (j+1) hj).band.1
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hw : 0 < w := div_pos (h₂ _ (cut₂.trans hjk)) (by norm_num)
  have power : 0 ≤ g^((p:ℝ)+1-η) := Real.rpow_nonneg hg.le _
  have hξ : 0 ≤ ξ := mul_nonneg (Nat.cast_nonneg _) power
  have env := Rep.envelope _ (sel.represents N n (j+1) hj).good
  apply kernel_tilt (C.path.levels.clock.op j n) (C.path.levels.blocks j n).branches Q.beta V
    Q.eval env (SectorNext.Vacuum.strictly C.path sel N n (j+1) hj) (localWilsonLog I g w Q.eval B)
    μ (by simp [μ,prior]) (localWilsonLog_meas I g w env.meas
      (continuous_bank L S T hj h t hS hjk p (Nat.le_succ p) g)).aemeasurable 0 ξ hξ _ F hF hM hb
  apply Filter.Eventually.of_forall
  intro U
  rw [sub_zero]
  exact local_log_estimate hg.ne' hw power Q.eval B I (rows (j+1) hjk hj T h t) U

end YM.Integration.FVA1Physical.Wilson

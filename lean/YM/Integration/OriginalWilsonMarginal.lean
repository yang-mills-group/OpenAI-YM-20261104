import YM.Integration.RetainedWilsonConditional
import YM.Integration.SelectedCofactorChamberMarginal
import YM.Integration.WilsonSpectatorReflection

/-! Exterior integration of the genuine fine Wilson step at each retained
coarse field, including signed marks on the full fine configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalWilsonMarginal

open Function Finset Set MeasureTheory Lattice Wilson RG
open WilsonKernelCoupling SelectedCofactorChamberMarginal Push.SectorMeasure.Env
open RetainedWilsonConditional
open scoped BigOperators Topology Classical

variable {G : Gauge} {c f : Side} (S : StepData c f) (A : Finset (Edge (Site c)))

private theorem all_equal {ι : Type*} (i j : Fintype ι) : @Finset.univ ι i = @Finset.univ ι j :=
  congrArg (fun f : Fintype ι => @Finset.univ ι f) (Subsingleton.elim i j)

/-- Integrating a single physical branch at a fixed retained configuration
leaves exactly the observed link factors, for every predicted field. -/
theorem noise_fiber (b : ℝ) (Q : Config G c) (x : A → G.El) :
    SelectedCofactorChamberMarginal.marginal (A : Set (Edge (Site c))) (S.noise b Q) x =
      branch S A b Q x := by
  let B := (A : Set (Edge (Site c)))ᶜ
  letI : Fintype B := @Subtype.fintype _ _ (fun i => Classical.propDecidable (i ∈ B)) _
  let e := cut G (A : Set (Edge (Site c)))
  let out (y : Fields G B) := ∏ i : B, link S b (Q i.val) (y i)
  have hl (y : Fields G B) (i : A) : e.symm (x,y) i.val = x i := by
    exact congr_fun (congrArg Prod.fst (e.apply_symm_apply (x,y))) i
  have hr (y : Fields G B) (i : B) : e.symm (x,y) i.val = y i := by
    exact congr_fun (congrArg Prod.snd (e.apply_symm_apply (x,y))) i
  have hnoise (V : Config G c) : S.noise b Q V = ∏ j, link S b (Q j) (V j) := by
    unfold StepData.noise link
    simp only [div_eq_mul_inv]
    exact prod_congr rfl fun _ _ => mul_comm _ _
  have hsplit (y : Fields G B) : S.noise b Q (e.symm (x,y)) = branch S A b Q x * out y := by
    rw [hnoise,←Fintype.prod_subtype_mul_prod_subtype (· ∈ A) (fun j => link S b (Q j) (e.symm (x,y) j))]
    simp_rw [hl,hr]
    congr 2 <;> exact all_equal _ _
  have hmass : ∫ y, out y ∂sheet G B = 1 := by
    dsimp only [out,sheet]
    have h := integral_fintype_prod_eq_prod (μ := fun _ : B => G.probHaar) (fun (i : B) => link S b (Q i.val))
    simpa only [link_mass,prod_const_one] using h
  change (∫ y, S.noise b Q (e.symm (x,y)) ∂sheet G B) = _
  simp_rw [hsplit]
  rw [integral_const_mul,hmass,mul_one]

/-- This is the original marginal, evaluated pointwise on all retained
links. The other links' normalized noise and every shared choice are kept. -/
theorem density_fiber (b : ℝ) (U : Config G f) (x : A → G.El) :
    SelectedCofactorChamberMarginal.marginal (A : Set (Edge (Site c))) (S.density b U) x =
      WilsonKernelCoupling.marginal S A b U x := by
  let B := (A : Set (Edge (Site c)))ᶜ
  let e := cut G (A : Set (Edge (Site c)))
  have hQ (Q : Config G c) : Envelope (S.noise b Q) := by
    refine ⟨((S.noise_cont b).comp (continuous_const.prodMk continuous_id)).measurable,
      Push.BetaTransport.noiseCost S |b|,fun V => ?_⟩
    rw [Real.norm_of_nonneg (Push.BetaTransport.noise_pos S b Q V).le]
    exact (Push.BetaTransport.noise_bounds S (le_refl _) Q V).2
  have hi t : Integrable (fun y : Fields G B => S.likelihood U t * S.noise b (S.prediction U t) (e.symm (x,y))) (sheet G B) :=
    (((hQ _).comp_env (e.symm.measurable.comp (measurable_const.prodMk measurable_id))).integrable _).const_mul _
  change (∫ y, ∑ t, S.likelihood U t * S.noise b (S.prediction U t) (e.symm (x,y)) ∂sheet G B) = _
  rw [integral_finsetSum _ (fun t _ => hi t)]
  unfold WilsonKernelCoupling.marginal
  apply sum_congr rfl
  intro t _
  rw [integral_const_mul]
  exact congrArg (fun y => S.likelihood U t * y) (noise_fiber S A b (S.prediction U t) x)

/-- At every retained configuration the literal exterior integral of the
original signed push is its sparse fine-Haar carrier. A finite original
L1 bound on the fine section suffices. -/
theorem pushed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : S.patch.Branches S.kernel G) (b : ℝ) {g : Config G f → E} (hg : Integrable g (prior G f)) (x : A → G.El) :
    SelectedCofactorChamberMarginal.marginal (A : Set (Edge (Site c))) (S.push b g) x = carrier S A b g x := by
  let B := (A : Set (Edge (Site c)))ᶜ
  let e := cut G (A : Set (Edge (Site c)))
  let d (U : Config G f) (y : Fields G B) := S.density b U (e.symm (x,y))
  have he : Envelope (fun q : Config G f × Fields G B => d q.1 q.2) :=
    (Push.GridApprox.den_env (S.isKernel h b)).comp_env (g := fun q : Config G f × Fields G B => (q.1,e.symm (x,q.2)))
      (measurable_fst.prodMk (e.symm.measurable.comp (measurable_const.prodMk measurable_snd)))
  have hi : Integrable (fun q : Config G f × Fields G B => d q.1 q.2 • g q.1) ((prior G f).prod (sheet G B)) :=
    smul_L1 (H:=fun q : Config G f × Fields G B => d q.1 q.2) (f:=fun q : Config G f × Fields G B => g q.1) he (hg.comp_fst (sheet G B))
  change (∫ y, ∫ U, d U y • g U ∂prior G f ∂sheet G B) = ∫ U, WilsonKernelCoupling.marginal S A b U x • g U ∂prior G f
  refine (integral_integral_swap (μ:=prior G f) (ν:=sheet G B) (f:=fun U y => d U y • g U) hi).symm.trans ?_
  apply integral_congr_ae
  apply ae_of_all
  intro U
  change (∫ y, d U y • g U ∂sheet G B) = WilsonKernelCoupling.marginal S A b U x • g U
  rw [integral_smul_const]
  exact congrArg (fun t : ℝ => t • g U) (density_fiber S A b U x)

open Extra.Histories Relay Bid OPE.Therm

/-- The positive exterior denominator of the actual original Wilson law is
precisely the positive fine carrier with the original adjacent coupling. -/
theorem physical {C : Family G} (hC : C.Makes) {N p i : ℕ} (hi : i < N)
    (D : Finset (Edge (Site (C.side i p)))) (x : D → G.El) :
    SelectedCofactorChamberMarginal.marginal (D : Set _) (C.path.rep N p i).eval x =
      carrier (C.path.levels.clock.op i p) D (C.path.β N p (i+1)) (C.path.rep N p (i+1)).eval x := by
  rw [(hC.wilson.steps N p i hi).1]
  exact pushed _ D (C.path.levels.blocks i p).branches _
    (((C.path.rep N p (i+1)).envelope (hC.wilson.represents N p (i+1) hi).good).integrable _) x

/-- The exact common fine Wilson partition provides the sparse lower and
upper bound of the original exterior vacuum. -/
theorem physical_bounds {C : Family G} (hC : C.Makes) {N p i : ℕ} (hi : i < N)
    (D : Finset (Edge (Site (C.side i p)))) (x : D → G.El) :
    let z := partition G (C.side N p) (C.path.β N p N)
    let m := SelectedCofactorChamberMarginal.marginal (D : Set _) (C.path.rep N p i).eval x
    let T := distortion (C.path.levels.clock.op i p) D (C.path.β N p (i+1)) 0
    z/T ≤ m ∧ m ≤ T*z := by
  intro z m T
  dsimp only [m]
  rw [physical hC hi]
  have hb := vacuum_bounds (C.path.levels.clock.op i p) D (C.path.levels.blocks i p).branches
    (C.path.β N p (i+1)) (((C.path.rep N p (i+1)).envelope (hC.wilson.represents N p (i+1) hi).good).integrable _)
    (fun U => (Multi.AxisShift.chosen_positive hC.wilson hi U).le) x
  rw [C.path.partition_eq hC.wilson N p (i+1) hi] at hb
  exact hb

end YM.Integration.OriginalWilsonMarginal

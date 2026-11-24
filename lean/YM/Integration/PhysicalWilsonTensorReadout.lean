import YM.Integration.IntrinsicWilsonTensor

/-! Uniform physical operator bounds for the original regulator's
multilinear intrinsic counterterm and all macroscopic Gram detectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonTensorReadout
open Function Filter Lattice Wilson OPE OPE.Orbits OPE.Cards PhysMS
open Frontier6.Road EngineeringWeightedReadout MultilinearCellCapture
open Trace.Pilot SharedIntrinsicWilsonGrid IntrinsicWilsonTensor
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

/-- Full physical detector with the reference-label tensor subtracted in
the original field frame. -/
def residual (U : Detector S D) (J : ℝ → PhysMS.tower S) (t : ℝ) (x : I → E4) (Z : Tensor C d D) :
    MultilinearMap ℂ (fun i => Input C (d i)) (Input C D) :=
  (wholeReadout U J t).toLinearMap.compMultilinearMap (MultilinearMap.pi (fun a =>
    let e := fun j => (OPE.tags S (U.listen a) j).1
    let w : Labels S e := fun j => (OPE.tags S (U.listen a) j).2
    (sectionLabels (d:=Sum.elim d e) w (Orbits.moment S (beside x (OPE.positions S (U.listen a)).ofLp))).compLinearMap
      (fun i => (J t (d i)).toLinearMap))) -
    ((J t D).symm.toLinearMap.comp (S.project D)).compMultilinearMap Z

theorem residual_apply (U : Detector S D) (J : ℝ → PhysMS.tower S) (t : ℝ) (x : I → E4)
    (Z : Tensor C d D) (v : (i : I) → Input C (d i)) :
    residual U J t x Z v = wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t x (S.project D (Z v))) := by
  let all (a : Fin U.size) := whole S x (Frame.born J t v) (OPE.positions S (U.listen a)).ofLp
    (fun j => (OPE.tags S (U.listen a) j).2)
  let single (a : Fin U.size) := witnessAt S D (U.listen a) (S.project D (Z v))
  change wholeReadout U J t _ - (J t D).symm (S.project D (Z v)) = wholeReadout U J t (all-single)
  rw [map_sub,show wholeReadout U J t single = (J t D).symm (S.project D (Z v)) from wholeReadout_field ..]
  apply congrArg (fun a => wholeReadout U J t a - (J t D).symm (S.project D (Z v)))
  funext a
  let e := fun j => (OPE.tags S (U.listen a) j).1
  let y := (OPE.positions S (U.listen a)).ofLp
  let w : Labels S e := fun j => (OPE.tags S (U.listen a) j).2
  exact sectionLabels_apply w (Orbits.moment S (d:=Sum.elim d e) (beside x y)) (Frame.born J t v)

private theorem expansion (M : MultilinearMap ℂ (fun i => Input C (d i)) (Input C D)) (v : (i : I) → Input C (d i)) :
    M v = ∑ q : IntrinsicWilsonTensor.Columns C d, Next.UVStress.coords (fun i => Input C (d i)) q v •
      M (Next.UVStress.combination (fun i => Input C (d i)) q) := by
  let b (i : I) := Module.finBasis ℂ (Input C (d i))
  have full : v = fun i => ∑ q, (b i).repr (v i) q • b i q := funext fun i => ((b i).sum_repr _).symm
  conv_lhs => rw [full]
  rw [M.map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact M.map_smul_univ _ _

/-- Every genuine joint intrinsic tensor obeys a physical operator estimate
uniform in all independent inputs and admitted central configurations. -/
theorem estimate (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i)) (U : Detector S D)
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J) :
    ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
      (∀ n : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (P.j t)^n * e t) trail (𝓝 0)) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
        ∀ Z : Tensor C d D, Common F R J t (P.b t) (P.j t) x Z →
          ∀ v : (i : I) → Input C (d i), ‖wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t
            (fun k => C.S.gridPoint (P.j t) (x k)) (S.project D (Z v)))‖ ≤ e t * ∏ i, ‖v i‖ := by
  let E := fun i => Input C (d i)
  let B := IntrinsicWilsonTensor.Columns C d
  let v₀ (q : B) := Next.UVStress.combination E q
  let coord (q : B) (i : I) := ((Module.finBasis ℂ (E i)).coord (q i)).toContinuousLinearMap
  let K (q : B) := ∏ i, ‖coord q i‖
  choose fee rate _ paid using fun q : B => SharedIntrinsicWilsonGrid.serve F facility anchor R P U J H (v₀ q)
  let e (t : ℝ) := ∑ q : B, K q * ‖fee q t‖
  have he : RateLE trail LogV e (-(1:ℝ)/32) := RateLE.sum PhysMS.to_log_zoom (fun q _ => by
    simpa only [zero_add] using (RateLE.const (K q) PhysMS.to_log_zoom).mul (rate q).norm)
  refine ⟨e,he,?_,?_⟩
  · intro n
    have hp : RateLE trail LogV e (-((0:ℕ):ℝ)-1/32) := by simpa only [Nat.cast_zero,neg_zero,zero_sub,neg_div] using he
    simpa only [Nat.cast_zero,zero_mul,Real.exp_zero,one_mul] using
      all_loop_orders PhysMS.to_log_zoom 0 _ hp P.fine n
  filter_upwards [eventually_all.mpr paid] with t measured
  intro x hx Z genuine v
  let y (i : I) := C.S.gridPoint (P.j t) (x i)
  let M := residual U J t y Z
  have basis (q : B) : ‖M (v₀ q)‖ ≤ ‖fee q t‖ :=
    ((show ‖M (v₀ q)‖ ≤ fee q t from by rw [show M = _ from rfl,residual_apply]; exact measured q x hx _ (genuine.cluster _))).trans (le_abs_self _)
  let V := ∏ i, ‖v i‖
  have cost (q : B) : ‖Next.UVStress.coords E q v‖ ≤ K q * V := by
    rw [Next.UVStress.coords,norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (coord q i).le_opNorm (v i))
  rw [← residual_apply]
  change ‖M v‖ ≤ e t*V
  rw [expansion M v,show e t*V = ∑ q : B, (K q*‖fee q t‖)*V from Finset.sum_mul ..]
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum fun q _ => by
    rw [norm_smul]
    exact (mul_le_mul (cost q) (basis q) (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg (fun i _ => (coord q i).opNorm_nonneg))
      (Finset.prod_nonneg (fun i _ => norm_nonneg _)))).trans_eq (by ring)

/-- Select one original tensor for all macroscopic detectors and inputs.
Every finite-scale selection uses a single actual cofinal subfilter. -/
theorem engineering (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i)) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J) :
    ∃ Z : ℝ → (I → Cover) → Tensor C d D,
      (∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
        Common F R J t (P.b t) (P.j t) x (Z t x)) ∧
      ∀ U : Detector S D, ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
        (∀ n : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (P.j t)^n * e t) trail (𝓝 0)) ∧
        ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
          ∀ v : (i : I) → Input C (d i), ‖wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t
            (fun k => C.S.gridPoint (P.j t) (x k)) (S.project D (Z t x v)))‖ ≤ e t * ∏ i, ‖v i‖ := by
  let existsAt (t : ℝ) (x : I → Cover) := ∃ Z : Tensor C d D, Common F R J t (P.b t) (P.j t) x Z
  let Z (t : ℝ) (x : I → Cover) : Tensor C d D := if h : existsAt t x then h.choose else 0
  have actual : ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
      Common F R J t (P.b t) (P.j t) x (Z t x) := by
    filter_upwards [common F facility anchor R P J H] with t stock
    intro x hx
    have h : existsAt t x := stock x hx
    simpa only [Z,dif_pos h] using h.choose_spec
  refine ⟨Z,actual,?_⟩
  intro U
  obtain ⟨e,he,loops,test⟩ := estimate F facility anchor R P U J H
  refine ⟨e,he,loops,?_⟩
  filter_upwards [test,actual] with t bound haveTensor
  exact fun x hx => bound x hx (Z t x) (haveTensor x hx)

end YM.Integration.PhysicalWilsonTensorReadout

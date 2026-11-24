import YM.MS.ScaleForest.TwoVertices
import YM.MS.Swirl.LandLine

/-!
# Full propagator and two parameters for the same dressing

We elect the **actual** `M=1` heat dressing of `A0`, retained IR
propagator `(1-H₁(ρ²p²))*P`, `ρ` length; zero at p=0. `halfP`, based on
the supplied `Fuel`, includes 1/2 (as do the shell kernels) and has color
identity. With the same packing of axes and ghosts this recovers the
filing's line including the FP sign at both ends. Provide the linear-length
(instead of log-length) version of the first bridge calculation too, for use
in doing the actual loop integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Function Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open City (LegsK)
open Momentum
open scoped Topology ContDiff
variable {G : Gauge} {n m h : ℕ} {b : Bool}

abbrev halfP (G : Gauge) (r : ℝ) : Rip G := fun _ => Landau.choir (Swirl.Near.Fuel r) id
abbrev radial (G : Gauge) (r : ℝ) : Rip G := fun _ => LegsK id r

theorem halfP_components (r : ℝ) (p : SectorP n) (i j : Cfield G n) :
    (2 : ℂ) * halfP G r n i j p =
      (1-(( (1+r^2*p.sq)*exp (-(r^2*p.sq)) :ℝ):ℂ))* Landau.choir Swirl.Near.Tail id i j p := by
  simp only [halfP, Landau.choir, id_eq, Swirl.Near.Fuel]; split <;> rename_i h
  rw [Swirl.Near.lown p r]; ring
  simp

theorem radial_log (G : Gauge) (t : ℝ) : A0 G t = (exp t : ℂ) • radial G (exp t) := by
  funext n i j q; unfold A0; simp only [radial,LegsK, Landau.choir,Pi.smul_apply,id_eq]; split
  · exact (City.brushed ..).symm
  exact (mul_zero _).symm

theorem radial_atOne (G : Gauge) : A0 G 0= radial G 1:= by simp [radial_log]

theorem continuous_radial (i j : Cfield G n) (p : SectorP n) : Continuous fun s => radial G s n i j p := by
  unfold radial LegsK Landau.choir; split
  swap
  · exact continuous_const
  rcases i with ⟨⟨_|a,_|_⟩,θ⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,κ⟩ <;>
    simp only [City.L0, id_eq] <;> try exact continuous_const
  all_goals unfold City.brush; fun_prop

theorem shell_deriv (i j : Cfield G n) (p : SectorP n) (r : ℝ) : HasDerivAt (fun s => halfP G s n i j p)
      (radial G r n i j p) r := by
  unfold halfP radial LegsK Landau.choir; split
  exact Swirl.Near.swing ..
  exact hasDerivAt_const ..

theorem propagator (s a : ℝ) (i j : Cfield G n) (p : SectorP n) :
    (∫ t in a..s, A0 G t n i j p) = halfP G (exp s) n i j p - halfP G (exp a) n i j p := by
  simp_rw [radial_log,Pi.smul_apply, smul_eq_mul, ← Complex.real_smul]; refine Eq.trans ?_
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := exp a) (b:=exp s) (fun x _ => shell_deriv i j p x)
      ((continuous_radial i j p).intervalIntegrable _ _))
  exact intervalIntegral.integral_deriv_smul_comp (fun t _ => Real.hasDerivAt_exp t)
    continuous_exp.continuousOn (continuous_radial i j p)

theorem halfP_nil (G : Gauge) (n : ℕ) : halfP G 0 n=0 := by
  funext i j q; unfold halfP Landau.choir Swirl.Near.Fuel
  rw [Swirl.Near.ohLow]; split <;> simp

theorem bridgeG_smul (G : Gauge) (K : Rip G) (c : ℂ) (A B : Mob G) :
    bridgeG (c•K) A B = c • bridgeG K A B := by
  funext m w; unfold bridgeG; simp only [Pi.smul_apply,smul_eq_mul]
  let L(i j : Cfield G m)(l r : Legs (Shore G m)) := Heat.radius Landau.parity (K m) i j (A m) (B m) l r
  let V l r:= ∑ i, ∑ j, L i j l r
  change _ = c * scatter (field parity) w V
  rw [show c * scatter (field parity) w V = _ from
    (show c * scatter _ w V = allocate (field parity) w (c • V) from (map_smul (allocate ..) c V).symm)]
  apply scatter_congr
  intro l r h; unfold V L Heat.radius
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem diff_bridge (w : Legs (Shore G m)) (F H : Mob G) (r : ℝ) :
    HasDerivAt (fun v => bridgeG (halfP G v) F H m w) (bridgeG (radial G r) F H m w) r := by
  have he (w : Legs (Shore G m)) (L : ℝ → Shared (Shore G m) ℂ) {L' : Shared (Shore G m) ℂ}
      (h : ∀ i j, HasDerivAt (fun x => L x i j) (L' i j) r) :
      HasDerivAt (fun x=> scatter (field parity) w (L x)) (scatter (field parity) w L') r := by
    induction w generalizing L L' with
    | nil => exact h [] []
    | cons i w ih => simp only [scatter_cons]; exact ih _ (fun l s => (h (i::l) s).add ((h ..).const_mul _))
  apply he; intro l s
  exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    ((((shell_deriv i j _ r).const_mul (2 : ℂ)).mul_const _).mul_const _)

theorem continuous_bridge (w : Legs (Shore G m)) (F H : Mob G) : Continuous fun t =>
    bridgeG (radial G t) F H m w := by
  have he (w : Legs (Shore G m)) (L : ℝ → Shared (Shore G m) ℂ) (h : ∀ i j, Continuous (fun x => L x i j)) :
      Continuous (fun x=> scatter (field parity) w (L x)) := by
    induction w generalizing L with
    | nil => exact h [] []
    | cons i w ih => simp only [scatter_cons]; exact ih _ (fun l s => (h (i::l) s).add (continuous_const.mul (h l (i::s))))
  apply he; intro l s
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_const.mul (continuous_radial i j (-net l))).mul continuous_const).mul continuous_const)

theorem integrated_bridge (b : Bool) (w : Legs (Shore G m)) (F H : Mob G) (s a : ℝ) :
    let c : ℂ := factor b
    (∫ t in a..s, c * bridgeG (A0 G t) F H m w) =
      ∫ r in (exp a)..(exp s), c * bridgeG (radial G r) F H m w := by
  intro c
  simp_rw [radial_log, bridgeG_smul,Pi.smul_apply,smul_eq_mul]; rw [intervalIntegral.integral_congr
    (g:=fun t : ℝ => exp t • (c * bridgeG (radial G (exp t)) F H m w))
    (fun i _ => by simp only [Complex.real_smul]; rw [mul_left_comm])]
  exact intervalIntegral.integral_deriv_smul_comp (fun t _ => Real.hasDerivAt_exp t)
    continuous_exp.continuousOn (continuous_const.mul (continuous_bridge w F H))

theorem aux_bridge (b : Bool) (w : Legs (Shore G m)) (F H : Mob G) (s : ℝ)
    (hp : IntegrableOn (fun t => (factor b : ℂ) * bridgeG (A0 G t) F H m w) (Set.Iic s)) :
    (∫ t in Set.Iic s, (factor b : ℂ) * bridgeG (A0 G t) F H m w) =
      (∫ t in (0:ℝ)..exp s, (factor b : ℂ)* bridgeG (radial G t) F H m w) := by
  let c : ℂ := factor b
  let A (t:ℝ) := c* bridgeG (A0 G t) F H m w
  let B (t:ℝ) := c* bridgeG (radial G t) F H m w
  have hC : Continuous B := continuous_const.mul (continuous_bridge w F H)
  let X (a:ℝ) := ∫ t in (0:ℝ)..a, B t
  have hX : X 0=0:= intervalIntegral.integral_same
  have he : ∀ᶠ a:ℝ in atBot, (∫ t in Iic s,A t) - ∫ t in Iic a,A t = X (exp s)-X (exp a) := by
    filter_upwards [eventually_le_atBot s] with a ha
    rw [intervalIntegral.integral_Iic_sub_Iic (hp.mono_set (Iic_subset_Iic.mpr ha)) hp]
    rw [integrated_bridge b w F H s a]
    linear_combination
      intervalIntegral.integral_add_adjacent_intervals (a:=0) (b:= exp a) (c:=exp s)
        (μ:=MeasureTheory.volume) (hC.intervalIntegrable _ _) (hC.intervalIntegrable _ _)
  have ht : Tendsto (fun a => (∫ t in Iic s,A t) - ∫ t in Iic a,A t) atBot (𝓝 (∫ t in Iic s,A t)) := by
    simpa only [sub_zero,id_eq] using (tendsto_integral_Iic_zero (f:=A) (μ:=MeasureTheory.volume) tendsto_id).const_sub
      (∫ t in Iic s,A t)
  have hT : Tendsto (fun a => X (exp a)) atBot (𝓝 0) := by
    rw [← hX]
    exact (( intervalIntegral.continuous_primitive (μ:=MeasureTheory.volume) (fun a b => (hC.intervalIntegrable ..)) _).continuousAt.tendsto).comp tendsto_exp_atBot
  refine tendsto_nhds_unique_of_eventuallyEq ?_ ?_ he
  · exact ht
  simpa only [sub_zero] using hT.const_sub (X (exp s))

theorem first_radial (A : LocalVertex G true 4) (B : LocalVertex G b h) (s : ℝ) :
    let R := firstSymbol A B (fullShell G)
    let c : ℂ := factor b
    plow (-(h:ℂ)) s R = (fun m w => ∫ t in (0:ℝ)..exp s, c* bridgeG (radial G t) A.symbol B.symbol m w) ∧
      plow (-(h:ℂ)) s R = c • bridgeG (halfP G (exp s)) A.symbol B.symbol := by
  intro R c
  obtain ⟨hx,hp,hV⟩ := first_integral A B (fullShell G) s
  dsimp only [fullShell] at hx hp
  simp_rw [pA] at hx hp
  have H : plow (-(h:ℂ)) s R = (fun m w => ∫ t in (0:ℝ)..exp s, c* bridgeG (radial G t) A.symbol B.symbol m w):= by
    unfold R fullShell; rw [hx]; funext m w; exact aux_bridge b w _ _ _ (hp m w)
  refine ⟨H,?_⟩
  rw [H]; funext m w
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i _=> (diff_bridge w A.symbol B.symbol i).const_mul c)
    ((continuous_const.mul (continuous_bridge w A.symbol B.symbol)).intervalIntegrable _ _)]
  have hZ : bridgeG (halfP G 0) A.symbol B.symbol = 0 := by
    rw [show halfP G 0=0 from funext (fun n=>halfP_nil G n),← zero_smul ℂ (0 : Rip G),
      bridgeG_smul,zero_smul]
  rw [hZ]; simp

end YM.MS.ScaleForest

import YM.Integration.WilsonThermometerSmallPanelColumns
import YM.Integration.WilsonPositionThermometerStationNorm

/-! Re-expression of the *same* finite group field on the paid small
reflection panel. Its cost is controlled by the original primary at k. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSmallPanelRead
open Function Filter Set Extraction Cells Wilson Lattice RG Spec Table Ward
open Next.Rank Next.Rank.Price Next.Rank.East Next.Rank.Station Next.Rank.Tapes.West
open MergeProof.East
open scoped Topology BigOperators Classical
variable {G : Gauge} (C : Family G)

def column (d k N p : ℕ) (b : ℝ) (T : Module.End ℂ (C.label d)) (v : C.label d) :
    C.label d := weightTag C d b⁻¹ ((C.labels.level d).scaled (shrink C k N p) (T v))

def scaleCost (d : ℕ) : ℝ := ∑ i : (C.labels.level d).Index, (2:ℝ)^((C.labels.level d).grades i).2

include C in
theorem recovers {d k N p : ℕ} (built : C.Makes) (start : C.ref d ≤ k) (late : k ≤ N)
    (b : ℝ) (hb : b≠0) (T : Module.End ℂ (C.label d)) (paid : Tested C d k N p T)
    (v : C.label d) : ladd C b k N p d T (column C d k N p b T v) = v := by
  let u := column C d k N p b T v
  obtain ⟨_,_,unique⟩ := solve C built start late paid u b
  apply (unique _ (poured built start late b T paid u)).trans (unique _ ?_).symm
  unfold Solves u column
  set y := (C.labels.level d).scaled (shrink C k N p) (T v)
  funext i
  change y i = (b:ℂ)^_ * ((b⁻¹:ℝ)^((C.labels.level d).grades i).1 * y i)
  rw [← mul_assoc,← mul_pow,← Complex.ofReal_mul,mul_inv_cancel₀ hb,Complex.ofReal_one,one_pow,one_mul]

private theorem small {k N p : ℕ} (built : C.Makes) (late : k ≤ N)
    (monitor : 1 ≤ C.path.levels.clock.monitor k) : shrink C k N p ≤ 2 := by
  let X := C.path.levels.clock.hatBeta k
  let B := C.path.β N p k
  have posX : 0 < X := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have posB : 0 < B := Overlay.beta_positive built.wilson late
  have band : X/2 ≤ B := (built.wilson.represents N p k late).band.1
  have sqrtX : Real.sqrt X ≤ 2*Real.sqrt B := by
    nlinarith [Real.sq_sqrt posX.le,Real.sq_sqrt posB.le,Real.sqrt_nonneg X,Real.sqrt_nonneg B]
  change (Real.sqrt B)⁻¹ / ((Real.sqrt X)⁻¹ * C.path.levels.clock.monitor k) ≤ 2
  have posM : 0 < C.path.levels.clock.monitor k := zero_lt_one.trans_le monitor
  field_simp [(Real.sqrt_pos.2 posB).ne',(Real.sqrt_pos.2 posX).ne',posM.ne']
  nlinarith [mul_nonneg (Real.sqrt_nonneg B) (sub_nonneg.mpr monitor)]

theorem price {d k N p : ℕ} (built : C.Makes) (late : k ≤ N)
    (monitor : 1 ≤ C.path.levels.clock.monitor k) (b : ℝ) (hb : 1≤b)
    (T : Module.End ℂ (C.label d)) (paid : Tested C d k N p T) (v : C.label d) :
    (C.labels.level d).coeffSize (column C d k N p b T v) ≤
      (2*scaleCost C d)*(C.labels.level d).coeffSize (awake C d k N p v) := by
  let F := C.labels.level d
  let t := shrink C k N p
  let w := awake C d k N p v
  have tpos := shrink_pos C built late p
  have tmax := small C (p:=p) built late monitor
  have positive := zero_lt_one.trans_le hb
  have swap : F.coeffSize (T v-w)=F.coeffSize (w-T v) := by
    unfold Labels.Frame.coeffSize
    exact Finset.sum_congr rfl (fun i _ => norm_sub_rev _ _)
  have a := Work.G08.size_triangle F (T v) w
  rw [swap] at a
  have change := paid.score v
  have raw : F.coeffSize (T v) ≤ 2*F.coeffSize w := by
    change F.coeffSize (w-T v) ≤ F.coeffSize w/2 at change
    linarith only [a,change,Work.G08.size_nonneg F w]
  have tariff (i : F.Index) :
      ‖column C d k N p b T v i‖ ≤ (scaleCost C d)*‖T v i‖ := by
    change ‖((b⁻¹:ℝ):ℂ)^(F.grades i).1 * (((t^(F.grades i).2 : ℝ):ℂ) * T v i)‖ ≤ _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos positive,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg tpos.le _),← mul_assoc]
    have first : b⁻¹ ^ (F.grades i).1 ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr positive.le) (inv_le_one_of_one_le₀ hb)
    have second : t^(F.grades i).2 ≤ (2:ℝ)^(F.grades i).2 :=
      pow_le_pow_left₀ tpos.le tmax _
    have weight : (2:ℝ)^(F.grades i).2 ≤ scaleCost C d :=
      Finset.single_le_sum (f:=fun j : F.Index => (2:ℝ)^(F.grades j).2)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul first second (pow_nonneg tpos.le _) zero_le_one).trans
        (by simpa using weight)) (norm_nonneg _)
  calc
    _ ≤ ∑ i, (scaleCost C d) * ‖T v i‖ := Finset.sum_le_sum (fun i _ => tariff i)
    _ = scaleCost C d * F.coeffSize (T v) := by rw [Labels.Frame.coeffSize,Finset.mul_sum]
    _ ≤ scaleCost C d * (2 * F.coeffSize w) :=
      mul_le_mul_of_nonneg_left raw (Finset.sum_nonneg (fun _ _ => by positivity))
    _ = _ := by ring

end YM.Integration.WilsonThermometerSmallPanelRead

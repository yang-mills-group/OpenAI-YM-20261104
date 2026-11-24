import YM.Integration.WilsonReportingUpperChartPrice
import YM.Integration.WilsonReportingUnitPrice
import YM.RG12.Canonical.Low

/-! The constant coefficient of the field prescribed at the reporting date,
including its engineering normalization at every later cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedUnit
open Function Filter Lattice Wilson RG Source Labels Extra.Histories RG12
open RG05Readout RG05Readout.Address WilsonReportingUnitOrbit
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {d m N p b:ℕ}

def scalar (C:Family G) (d:ℕ) (x:C.label d) : C.label d := x 0 • (C.labels.level d).e0

theorem upper (h:C.Makes) (age:C.ref d ≤ m) (live:m ≤ N) (x:C.label d) :
    chunk (primary d) ((C.factory d N p).terminal.symm (atK C h d m (N,p) (scalar C d x))) =
    coordinate C d N (x 0/(C.S.a m:ℂ)^d) := by
  let z:=x 0/(C.S.a m:ℂ)^d
  have pos:(C.S.a m:ℂ)≠0:=by exact_mod_cast (C.S.a_pos m).ne'
  have eq:scalar C d x=z • unitVec (C.labels.level d) C.path m:=by
    unfold scalar unitVec
    rw [smul_smul]
    change x 0 • _ = (x 0/(C.S.a m:ℂ)^d*(C.S.a m:ℂ)^d) • _
    rw [div_mul_cancel₀ _ (pow_ne_zero _ pos)]
  rw [eq,map_smul,atK_unit h d m (N,p) age live,map_smul,Charts.terminal_unit_vec C h d N p (age.trans live)]
  change chunk (primary d) (z • ((C.S.a N:ℂ)^d • (C.labels.level d).e0)) =
    ((C.S.a N:ℂ)^d*z) • (chunk (primary d) (C.labels.level d).e0)
  funext t
  by_cases ht:t=primary d
  · subst t
    rw [Pi.smul_apply,chunk_self,chunk_self,smul_smul,mul_comm]
    rfl
  · rw [Pi.smul_apply,chunk_miss _ ht,chunk_miss _ ht,smul_zero]

theorem paid (h:C.Makes) {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d p} {U:Emblems C d}
    (spine:Spine D B h b p d N V U) (x:C.label d) (start:b ≤ m) (age:∀ i ≤ d,C.ref i ≤ m) (live:m ≤ N) :
    size (WilsonReportingUpperChartPrice.returned h (primary d) (scalar C d x) U m N p) ≤
      (‖x 0‖/‖phase‖)*WilsonReportingUnitPrice.bound C d := by
  unfold WilsonReportingUpperChartPrice.returned
  change size (Many.point U (chunk (primary d) ((C.factory d N p).terminal.symm (atK C h d m (N,p) (scalar C d x)))) N m) ≤ _
  rw [upper (p:=p) h (age d le_rfl) live x]
  refine (WilsonReportingUnitPrice.original h spine m live start age _).trans_eq ?_
  have pos:((C.S.a m)^d)≠0:=pow_ne_zero _ (C.S.a_pos m).ne'
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos m).le]
  field_simp

theorem affordable (h:C.Makes) (simple:G.Simple) (d e:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ {N p b:ℕ} {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d p} {U:Emblems C d},
    Spine D B h b p d N V U → b ≤ m → m ≤ N → ∀ x:C.label d,
    mass C d x ≤ (C.path.levels.clock.hatBeta m)^e →
    size (WilsonReportingUpperChartPrice.returned h (primary d) (scalar C d x) U m N p) ≤
      (C.path.levels.clock.hatBeta m)^(e+1) := by
  let K:=WilsonReportingUnitPrice.bound C d/‖phase‖
  have nonneg:0 ≤ WilsonReportingUnitPrice.bound C d:=by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_trans zero_le_one (Push.Local.probe_budget (C.labels.level (kept i))).choose_spec.choose_spec.1)
      (Native.Cap.cost (Native.line i) 0).choose_spec.1.le
  have positive:0 ≤ K:=div_nonneg nonneg (norm_nonneg _)
  filter_upwards [(Next.Rank.Station.hat_rate C.path.levels simple).eventually_ge_atTop K,eventually_ge_atTop ((Finset.Iic d).sup C.ref)] with m enough late
  intro N p b D B V U spine start live x submit
  have age:∀ i ≤ d,C.ref i ≤ m:=fun i hi=>(Finset.le_sup (f:=C.ref) (Finset.mem_Iic.mpr hi)).trans late
  have component:‖x 0‖ ≤ mass C d x:=
    Finset.single_le_sum (f:=fun i=>‖x i‖) (fun i _=>norm_nonneg _) (Finset.mem_univ 0)
  have beta:0 ≤ C.path.levels.clock.hatBeta m:=(C.path.levels.fits.delayed m).le.trans' zero_le_one
  calc
    _ ≤ (‖x 0‖/‖phase‖)*WilsonReportingUnitPrice.bound C d := paid h spine x start age live
    _ = ‖x 0‖*K := by dsimp [K]; ring
    _ ≤ (C.path.levels.clock.hatBeta m)^e*K := mul_le_mul_of_nonneg_right (component.trans submit) positive
    _ ≤ _ := by rw [pow_succ]; exact mul_le_mul_of_nonneg_left enough (pow_nonneg beta _)

end YM.Integration.WilsonReportingPrescribedUnit

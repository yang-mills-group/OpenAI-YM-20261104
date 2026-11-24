import YM.Integration.FVA1Physical.Wilson.FluctuationPurchase
import YM.Integration.FVA1Physical.Round2.StageThreshold
import YM.Integration.FVA1Physical.Wilson.CoarseGate

/-! The genuine thermal collar on one blocking step lies in the next step's
scaled chart. The ratio is paid uniformly in all periods by a native stage
threshold independent of the field or either measured coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Lattice RG YM.Wilson MSbar MSbar.Mosaic MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage Precision
open YM.Integration.FVA1Physical.Wilson Qlocal.Schedule
open scoped Classical Topology
variable {G:Gauge}

theorem thermal_step (simple:G.Simple) (P:Patch) : ∀ᶠ x:ℝ in atTop,
    room x ≤ 2*room (tip G P.L x) := by
  let a:=-(1/2:ℝ)
  have ratio:=(Mosaic.Run.shift (X:=fun x:ℝ=>x) tendsto_id tendsto_id G simple P.L a).2
  have rev:Tendsto (fun x:ℝ=>x^a/(tip G P.L x)^a) atTop (𝓝 1):=by
    simpa only [inv_div,inv_one] using ratio.inv₀ one_ne_zero
  have c:0 ≤ G.slopeConstant*Real.log P.L.val :=
    mul_nonneg (Gauge.slopeConstant_pos simple).le (Real.log_nonneg (Nat.one_le_cast.mpr P.L.property))
  filter_upwards [rev.eventually (ge_mem_nhds one_lt_two),eventually_gt_atTop (1:ℝ)] with x bound large
  let y:=tip G P.L x
  have xy:x ≤ y:=by change x ≤ x+_; linarith only [c]
  have hx:=zero_lt_one.trans large
  have hy:0 < y:=hx.trans_le xy
  have power:x^a ≤ 2*y^a:=(div_le_iff₀ (Real.rpow_pos_of_pos hy a)).mp bound
  have log:=Real.log_le_log hx xy
  have lx:=Real.log_nonneg large.le
  have ly:0 ≤ Real.log y:=lx.trans log
  have t:=mul_le_mul power log lx (mul_nonneg zero_le_two (Real.rpow_nonneg hy.le a))
  have both:=mul_le_mul t (Real.sqrt_le_sqrt log) (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg zero_le_two (Real.rpow_nonneg hy.le a)) ly)
  exact both.trans_eq (by change 2*y^a*Real.log y*Real.sqrt (Real.log y)=2*(y^a*Real.log y*Real.sqrt (Real.log y)); ring)

def thermalInvoice (hG:G.Simple) : Goal G := selectedThreshold (G:=G)
  (fun _ _ P _=>(eventually_atTop.mp (thermal_step hG P)).choose)

theorem thermalInvoice_obtainable (hG:G.Simple) : Obtainable (thermalInvoice hG) :=
  selectedThreshold_obtainable _

theorem thermal_steps_on (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (r:thermalInvoice hG R.metals R.rolls R.alloy R.kit) (j n:ℕ) :
    room (R.family.path.levels.clock.hatBeta j) ≤ 2*room (R.family.path.levels.clock.hatBeta (j+1)) := by
  have shift:tip G (R.family.path.levels.clock.op j n).patch.L (R.family.path.levels.clock.hatBeta j)=
      R.family.path.levels.clock.hatBeta (j+1):=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  rw [←shift]
  exact (eventually_atTop.mp (thermal_step hG (R.family.path.levels.clock.op j n).patch)).choose_spec _ (r j n)

theorem regularInputs_thermal {f:Side} (U:Config G f) {g h A x y:ℝ}
    (hg:0 < g) (hh:0 < h) (hA:0 ≤ A) (roomPaid:room x ≤ 2*room y)
    (live:U∈regularInputs g (A*room x/g)) : U∈regularInputs h (2*A*room y/h) := by
  refine ⟨live.1,?_⟩
  have identity:chartLog h U = (g/h) • chartLog g U := by
    unfold chartLog
    rw [smul_smul]
    congr 1
    field_simp
  change ‖chartLog h U‖ ≤ 2*A*room y/h
  rw [identity,norm_smul,Real.norm_of_nonneg (div_nonneg hg.le hh.le)]
  apply (mul_le_mul_of_nonneg_left live.2 (div_nonneg hg.le hh.le)).trans
  have q:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left roomPaid hA) hh.le
  calc g/h*(A*room x/g)=A*room x/h:=by field_simp
       _ ≤ A*(2*room y)/h:=q
       _=_:=by ring
end YM.Integration.FVA1Physical.Round2.Curvature

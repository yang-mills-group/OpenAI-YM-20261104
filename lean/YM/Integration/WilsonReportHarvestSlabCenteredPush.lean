import YM.Integration.WilsonReportHarvestSlabCubic
import YM.Integration.WilsonSeparatedOriginalSlabReturn

/-! Translation by a fixed older measured value commutes with the original
linear Wilson push on a signed difference of three-field sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabCenteredPush
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonReportHarvestSlabLabels WilsonReportHarvestSlabShiftLabels
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}
local notation "S" => Stock.census (Fin 3)

def score (v:Fin 3→ℂ):Poly S →L[ℂ] ℂ:=(Poly.get entire).comp
  (LinearMap.mulLeft ℂ (Poly.pass (Mach S v))).toContinuousLinearMap

private theorem step {c n:Side}{op:StepData c n}{β:ℝ} (valid:op.IsKernel β G)
    (f:Poly S →L[ℂ] ℂ){F:Config G n → Poly S}(live:Integrable F (prior G _)):
    (fun U=>f (op.push β F U))=op.push β (fun W=>f (F W)):=by
  let L:=f.restrictScalars ℝ
  funext U;unfold StepData.push
  have line:=L.integral_comp_comm (StepData.push_slice valid U F live)
  simp_rw [L.map_smul] at line
  exact line.symm

theorem through (A:History G)(N per:ℕ){u n:ℕ} (F:Config G (A.S.side n per)→Poly S)
    (live:Integrable F (prior G _)) (age:u≤n)(f:Poly S →L[ℂ] ℂ):
    (fun U=>f (gust A N per n F u age U))=pushTo A N per age (fun W=>f (F W)):=by
  induction age using Nat.decreasingInduction with
  | self=>rw [gust_base,pushTo_self]
  | of_succ i hi ih=>
    rw [gust_step A N per n F hi,Birth.push_first A N per hi]
    exact (step (A.levels.transition_mass ..) f (gust_live A N per _ _ live hi)).trans (by rw [ih])

def value (A:History G)(N per:ℕ){u n:ℕ}(age:u≤n)(F L:Config G (A.S.side n per)→Poly S)
    (v:Fin 3→ℂ)(V:Config G (A.S.side u per)):ℂ:=
    pushTo A N per age (fun W=>(translated v (F W)).part entire-(translated v (L W)).part entire)
      V/liftVac A N per u V

theorem held (A:History G)(N per:ℕ){u n:ℕ}(age:u≤n)(F L:Config G (A.S.side n per)→Poly S)
    (full:Integrable F (prior G _))(keep:Integrable L (prior G _))
    (zero:∀W,(F W).part (S).quiet=(L W).part (S).quiet)
    (single:∀i W,(F W).part ((S).fire i)=(L W).part ((S).fire i))
    (v:Fin 3→ℂ)(U:Config G (A.S.side u per)):
    value A N per age F L v U=value A N per age F L 0 U+
      ∑i:Fin 3,v i*(value A N per age F L (Pi.single i 1) U-value A N per age F L 0 U):=by
  let X:=gust A N per n F u age U-gust A N per n L u age U
  have slot (cell:(S).Mode)(agree:∀W,(F W).part cell=(L W).part cell):X.part cell=0:=by
    change (gust A N per n F u age U).part cell-(gust A N per n L u age U).part cell=0
    apply sub_eq_zero.mpr
    rw [congr_fun (gust_choose A N per F full age cell) U,congr_fun (gust_choose A N per L keep age cell) U,
      funext agree]
  have paid (c:Fin 3→ℂ):value A N per age F L c U=(score c) X/liftVac A N per u U:=by
    unfold value
    change pushTo A N per age (fun W=>score c (F W)-score c (L W)) U/_=_
    have first:Integrable (fun W=>score c (F W)) (prior G _):=((score c).restrictScalars ℝ).integrable_comp full
    have last:Integrable (fun W=>score c (L W)) (prior G _):=((score c).restrictScalars ℝ).integrable_comp keep
    rw [WilsonSeparatedOriginalSlabReturn.difference A N per age _ _ first last]
    change (pushTo A N per age (fun W=>score c (F W)) U-pushTo A N per age (fun W=>score c (L W)) U)/_= _
    rw [←congr_fun (through A N per F full age (score c)) U,←congr_fun (through A N per L keep age (score c)) U]
    rw [show score c X=(score c) (gust A N per n F u age U)-(score c) (gust A N per n L u age U) from map_sub ..]
  have exactRow:score v X=score 0 X+∑i:Fin 3,v i*(score (Pi.single i 1) X-score 0 X):=
    WilsonReportHarvestSlabCubic.raised X (slot _ zero) (fun i=>slot _ (single i)) v
  simp_rw [paid]
  rw [exactRow,add_div,Finset.sum_div]
  congr 1;apply Finset.sum_congr rfl;intro i _;ring

theorem charged (f:(Fin 3→ℂ)→ℂ)(v:Fin 3→ℂ)
    (line:f v=f 0+∑i:Fin 3,v i*(f (Pi.single i 1)-f 0))
    {b:ℝ}(zero:‖f 0‖≤b)(one:∀i:Fin 3,‖f (Pi.single i 1)‖≤b):
    ‖f v‖≤(1+2*∑i:Fin 3,‖v i‖)*b:=by
  rw [line]
  apply (norm_add_le ..).trans
  have each (i:Fin 3):‖v i*(f (Pi.single i 1)-f 0)‖≤‖v i‖*(b+b):=by
    rw [norm_mul];exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (one i) zero)) (norm_nonneg _)
  apply (add_le_add zero ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>each i)))).trans_eq
  rw [←Finset.sum_mul];ring

end YM.Integration.WilsonReportHarvestSlabCenteredPush

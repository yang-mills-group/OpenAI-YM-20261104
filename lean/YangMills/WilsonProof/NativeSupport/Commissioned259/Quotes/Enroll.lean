import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.August
/-! # Two-scale comparison in actual MoveSpace & our earlier basis-norm dollars -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ}
variable {R Q P: I→Operator G d} {w v:I→ℝ}
-- entrywise Pt, operator orientation
abbrev Issue (L:Filter I) (w:I→ℝ) (A:I→Operator G d) := (stiffness ∘ A)=O[L] w
lemma Issue.plus (h:Issue L w R) (hp:Issue L w P) : Issue L w (fun i=> R i+P i) := matrixPay.mpr fun i j=>(matrixPay.mp h i j).add (matrixPay.mp hp i j)
lemma Issue.subtract (h:Issue L w R) (hp:Issue L w P) : Issue L w (fun i=>R i-P i) := matrixPay.mpr fun i j=>(matrixPay.mp h i j).sub (matrixPay.mp hp i j)
lemma Issue.mult (h:Issue L w R) (hp:Issue L v P) : Issue L (fun i=>w i*v i) (fun i=>R i*P i) := matrixPay.mpr fun i j=> IsBigO.sum (s:=Finset.univ) (fun k _=> (matrixPay.mp h i k).mul (matrixPay.mp hp k j))
lemma Issue.multiply (h:Issue L Pose.home R) (hp:Issue L Pose.home P) : Issue L Pose.home (fun i=>R i*P i) := Issue.mult h hp |>.congr_right (fun i=> one_mul _)
lemma Issue.coverage {A:Operator G d}(h:Tendsto R L (𝓝 A)): Issue L Pose.home R := matrixPay.mpr fun i j=> isBigO_const_of_tendsto (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j ) one_ne_zero
lemma Issue.recover {Q:Operator G d} (h:Issue L w (fun i=>R i-Q))(v:Tendsto w L (𝓝 0)) : Tendsto R L (𝓝 Q) := by
  refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> (tendsto_sub_nhds_zero_iff).mp ?_; exact (matrixPay.mp h i j).trans_tendsto v
lemma Charge (A : Normalize.Guard G d)(x p) : columns (accepts A p x)= (fun b c=> crop p x (prose A b c)) := funext fun b=> funext fun c=>sum_coords ..
-- guide vs columns. Need BACK direction for chart stability on trials.
def atGuide (G:Gauge)(d:ℕ) : MoveSpace G d →ₗ[ℝ] (Toon G d → Toon G d→ℂ) where
   toFun x:= columns ((guide G d).symm x).val
   map_add' a b:= by rw [map_add]; ext i j; exact map_add (coord i) _ _
   map_smul' a b:= by rw [map_smul]; ext1 i; ext1 j; exact map_smul ((coord i).restrictScalars ℝ) _ _
lemma ensign (X:I→Change G d)(h:Tendsto (fun i=>columns (stand (X i))) L (𝓝 1)): Tendsto (fun i=>guide G d (X i)) L (𝓝 0) := by
  let C:= atGuide G d
  have eq i : C (guide G d (X i))= columns (stand (X i)) - (1:Operator G d) := by
    ext1 j; ext1 k; change coord j (((guide G d).symm _).val (theory k))=(columns _ - _) j k; rw [ LinearEquiv.symm_apply_apply, ← one_matrix, Matrix.sub_apply,columns,stood, map_add]; change _ = _ +_ - coord j (theory k); abel
  have hi: LinearMap.ker C=⊥:= by
    apply le_antisymm _ bot_le; intro v hv; apply (Submodule.mem_bot ..).mpr;
    let u:=(guide G d).symm v; have h0 : u = 0 := by
      apply Subtype.ext; ext1 x; change u.val x = 0; rw [← all_sig x, map_sum]; apply Finset.sum_eq_zero; intro i _
      have he:u.val (theory i)=0:= by
        rw [ ← all_sig (u.val (theory i))]; apply Finset.sum_eq_zero; intro j _; have hh:= congr_fun (congr_fun (LinearMap.mem_ker.mp hv) j) i; change coord j (u.val (theory i))=0 at hh; change coord j (u.val (theory i)) • theory j = 0; rw [ hh, zero_smul ]
      rw [_root_.map_smul,he, smul_zero]
    exact (guide G d).apply_symm_apply _ |>.symm.trans ((congr_arg (guide G d) h0).trans (map_zero _))
  let M:= C.leftInverse; have hm i : (guide G d) (X i)= M (columns (stand (X i)) - (1:Operator G d)) := by rw [← eq]; exact Eq.symm (LinearMap.leftInverse_apply_of_inj hi _)
  have hp := h.sub (tendsto_const_nhds (x:=(1:Operator G d))); rw [sub_self] at hp; rw [ ← map_zero M]
  exact ((M.continuous_of_finiteDimensional.continuousAt (x:=0)).tendsto.comp hp).congr (fun i=> (hm i).symm)

abbrev Shrinks (L:Filter I) (R:I→Operator G d) := Tendsto R L (𝓝 0)
lemma shrink {P : Operator G d} (h:Tendsto R L (𝓝 P)) : Shrinks L (fun i=>R i-P) := by have hp:= h.sub (tendsto_const_nhds (x:=P)); rwa [sub_self] at hp
lemma shrink_into (h:Issue L w R) (ht:Tendsto w L (𝓝 0)) : Shrinks L R := tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>(matrixPay.mp h i j).trans_tendsto ht
lemma Slimness : Shrinks L R ↔ ∀ i j:Toon G d,(fun k=> R k i j)=o[L] Pose.home := by
  constructor
  · intro h i j; exact (isLittleO_one_iff ℝ).mpr (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j)
  intro h; exact tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> (isLittleO_one_iff ℝ).mp (h i j)
lemma shrink_l (h:Issue L Pose.home R)(hp:Shrinks L P): Shrinks L (fun i=> R i * P i) := Slimness.mpr (fun i j=> IsLittleO.sum (s:=Finset.univ) (fun k _=> ((matrixPay.mp h i k).mul_isLittleO (Slimness.mp hp k j)).congr_right fun i=>one_mul _))
lemma shrink_r (hp:Shrinks L P)(h:Issue L Pose.home R) : Shrinks L (fun i=> P i * R i) := Slimness.mpr (fun i j=> IsLittleO.sum (s:=Finset.univ) (fun k _=> ((Slimness.mp hp i k).mul_isBigO (matrixPay.mp h k j)).congr_right fun i=>one_mul _))
lemma shrink_plus (h:Shrinks L R)(hp:Shrinks L P) : Shrinks L (fun i=>R i+P i) := by
  have h:= Tendsto.add h hp; rwa [add_zero] at h
lemma esc_contract {V : Operator G d} (h: Shrinks L (fun i=> R i - V)) : Tendsto R L (𝓝 V) :=
  Tendsto.congr (fun i=> sub_add_cancel (R i) V) (by simpa only [zero_add] using ( Tendsto.add h (tendsto_const_nhds (x:=V)) ))
lemma contraction_hyp {S T:I→Operator G d}(h:Shrinks L (fun i=>R i-S i))(k:Shrinks L (fun i=>P i-T i))(b:Issue L Pose.home S)(c:Issue L Pose.home P) : Shrinks L (fun i=> R i*P i - S i*T i) :=
   Tendsto.congr (fun i=> by rw [mul_sub,sub_mul]; abel) (shrink_plus (shrink_l b k) (shrink_r h c))
theorem unity (h:Tendsto R L (𝓝 1))(he:∀ᶠ i in L,R i*P i=1) : Tendsto P L (𝓝 1) := by
  have e : ContinuousAt Ring.inverse (1:Operator G d).det := by rw [Ring.inverse_eq_inv',det_one]; exact continuousAt_inv₀ one_ne_zero
  have hc: Tendsto (fun i=>(R i)⁻¹) L (𝓝 1) := by simpa [Function.comp_def] using (continuousAt_matrix_inv (1:Operator G d) e).tendsto.comp h
  apply hc.congr'; filter_upwards [ (continuous_id.matrix_det.tendsto _ |>.comp h).eventually (eventually_ne_nhds (by simp : (1:Operator G d).det≠0)), he ] with i h e
  change (R i).det ≠ 0 at h
  nth_rw 1 [ ← mul_one ((R i)⁻¹), ←e, ← mul_assoc,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h),one_mul ]
end YM.FVA2.GradedFar259.Quotes

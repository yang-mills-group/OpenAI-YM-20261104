import YM.Pert.Scale.Measure
import YM.Pert.Scale.ControlInverse
import YM.Pert.Scale.ScaleStress
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Scale
open Function Set Topology Filter RawLabels Position Extra.FD Maxwell Spec Analysis Climb UVNext.FreeStress
open scoped ContDiff Topology
variable {G : Gauge} {C : Family G} {I : Extraction.Order} {S : Table C.book} {n d : ℕ} {b : Final C I S} {X : Scaling S}

lemma gear_stress (F : Labels.Frames G) (t : ℝ) (i j : Axis) : gear F 4 t (freeStress F i j) = (t:ℂ)^4 • freeStress F i j := by
   have he (a b c d : Axis) : gear F 4 t (flat F a b c d) = (t:ℂ)^4 • flat F a b c d := by
     change gear F 4 t (enroll F 4 (ff G 4 le_rfl a b c d))=_
     rw [gear_inherit, grow_weights (p:=ff G 4 le_rfl a b c d) (w:=4) (graded_tape (initialPlace a b) (initialPlace c d)) t,map_smul]; rfl
   have hp (i j) : gear F 4 t (panel F i j) = (t:ℂ)^4 • panel F i j := by rw [panel,map_sum,Finset.smul_sum]; simp only [he]
   have ht : gear F 4 t (total F) = (t:ℂ)^4 • total F := by rw [total,map_sum,Finset.smul_sum]; exact Finset.sum_congr rfl fun k _=> hp k k
   rw [freeStress,← common_stress,UVNext.FreeStress.torch]; simp only [Pi.neg_apply,one_smul,map_neg,smul_neg,neg_inj]
   unfold canonicalStress; rw [map_sub,smul_sub,hp]; split <;> first | (simp only [map_smul,ht]; rw [smul_comm]) | simp

variable (h : FirstExtension b X)
section inverse
variable {Q : Conditions C.labels d n} {φ : Ledger Q → Buffer C.labels d} (hq : CleanProfiles Q) (hl : Reports (chart Q) (white Q) 0 φ)
include h hq hl
/-- Leading intertwiner between two bounded-ratio positions along the patch, with the inverse frame on the left. No precision asserted for transforming a coupling-power remainder all the way to fixed physical fields. `s,t` relative lengths. -/
lemma step_limit (s t) (hs : 0<s) (ht : 0<t) (v : E C.labels d) :
  Tendsto (fun k : ℕ => (positionScale X φ k s).symm ((positionScale X φ k t) v)) atTop (𝓝 (gear C.labels d (t/s) v)) := by
  let J := gearIso C.labels d s hs
  let a k := relative X φ k t v
  have hh := control_inverse (fun k=>relative X φ k s) J a (a₀:=gear C.labels d t v) (fun p=>(relative_leading h hq hl hs p).1) ((relative_leading h hq hl ht _).1)
  have he : J.symm (gear C.labels d t v)=_ := congrArg J.symm (show gear C.labels d t v=J (gear C.labels d (t/s) v) from Eq.symm ((gear_chain C.labels s (t/s) v).trans (congrArg (fun r => gear C.labels d r v) (mul_div_cancel₀ t hs.ne'))))
  rw [J.symm_apply_apply] at he
  rw [he] at hh
  apply hh.congr; intro k; simp only [a,positionScale,LinearEquiv.symm_trans_apply,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] -- lemma name

omit h hq hl in
def dressedLie (F : Labels.Frames G) (d : ℕ) (i : Axis×Axis) (t : ℝ) (v : E F d) :=
    ((Free.gear F).lie d (Spin.K i)) (gear F d t v)
set_option maxHeartbeats 1800000 in
/-- Same-field comparison of physical rotational matrices at leading order, including rotation of the positions and without asking the finite calibration to commute exactly with continuous rotations. -/
lemma turn_limit (s) (hs : 0<s) (i : Axis × Axis) (v : E C.labels d) :
   Tendsto (fun k : ℕ => Spin.transport b.sector.turns.lie (positionScale X φ k s) i v) atTop (𝓝
       ((gearIso C.labels d s hs).symm (dressedLie C.labels d i s v))) := by
   let a k := Spin.transport b.sector.turns.lie (X.U k d) i
   let z k := relative X φ k s v
   have htC : Continuous (fun M : (E C.labels d→L[ℂ]E C.labels d) × E C.labels d => M.1 M.2) := isBoundedBilinearMap_apply.continuous
   have hv : Tendsto (fun k => z k) atTop (𝓝 (gear C.labels d s v)) := (relative_leading h hq hl hs v).1
   have ht : Tendsto (fun k => a k (z k)) atTop (𝓝 (dressedLie C.labels d i s v)) := by
      have hp := h.rotations i d
      exact htC.continuousAt.tendsto.comp (hp.prodMk_nhds hv)
   exact control_inverse (fun k=>relative X φ k s) _ _ (fun p=> (relative_leading h hq hl hs p).1) ht
end inverse
variable {Q : Conditions C.labels 4 n} {φ : Ledger Q → Buffer C.labels 4} (hq : CleanProfiles Q) (hl : Reports (chart Q) (white Q) 0 φ)
include h hq hl
lemma measured_stress (i j : Axis) {s : ℝ} (hs : 0<s) :
   Tendsto (fun k => (positionScale X φ k s).symm ((↑((s*X.r k)^4 : ℝ):ℂ) • b.sector.energy i j)) atTop (𝓝 (freeStress C.labels i j)) := by
   let A := gear C.labels 4 s (freeStress C.labels i j)
   let u := fun k => (s:ℂ)^4 • movingTensor b X i j k
   have ht : Tendsto u atTop (𝓝 A) := by unfold A; rw [gear_stress]; exact (stress_readback h i j).const_smul ((s:ℂ)^4)
   have hv := control_inverse (fun k=>relative X φ k s) (gearIso C.labels 4 s hs) u (a₀:=A) (fun p=>(relative_leading h hq hl hs p).1) ht
   have hh : (gearIso C.labels 4 s hs).symm A=freeStress C.labels i j := LinearEquiv.symm_apply_apply .. 
   rw [hh] at hv
   apply hv.congr; intro k
   simp only [u, movingTensor,positionScale, mul_pow,Complex.ofReal_pow,Complex.ofReal_mul,map_smul, mul_smul]; rfl
end YM.Pert.Scale

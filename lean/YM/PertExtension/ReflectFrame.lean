import YM.PertExtension.FlagPosition
import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis

/-! Positive reflected bilinear test form averaged over signed axes, and
relation between zero of the direction-LM on the finite-coordinate
pre-group and ordinary two-point Ward skew in the Wick comparator fields.
This step uses no perturbative interaction identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.PertExtension.Rigidity
open Set Function Filter MeasureTheory Labels MvPolynomial Table Climb Ward Maxwell
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {G : Gauge}{J:Type*}[Fintype J][DecidableEq J] (F : Frames G)
variable {d : ℕ}
namespace Positive
open Tensor Analysis Maxwell.Free Extra.FD

private lemma face_axis_eval (a:Axis) : Extra.FD.faceM (_root_.YM.basis a) = (Signed.reflect a).val := by
  ext i j
  simp only [Extra.FD.faceM,Extra.FD.rr, Matrix.of_apply, reflect_entry,parity]
  have ht : ‖_root_.YM.basis a‖=1:=YM.basis_norm _
  simp [ht,YM.basis, EuclideanSpace.single_apply]
  grind

private lemma rides (s : Signed)(v:(Model F).Field d): ride F s.ortho d v = (Model F).mirror (table_spin F) d s v := by
  apply writes_inj F d
  obtain ⟨u,rfl⟩:=Table.onto _ _ v
  rw [ride_at,Table.mirror_project,writes_project,writes_project]
  exact (Extra.FD.polish_act ..).symm

private lemma face_mirror (a : Axis)(F:Frames G)(v:(Model F).Field d) :
    Extra.FD.faceTest F d (_root_.YM.basis a) 0 v=(Model F).adj (table_spin F) d a v:= by
   unfold Extra.FD.faceTest Table.adj
   rw [sub_zero, show Extra.FD.face (_root_.YM.basis a)= Signed.reflect a from Subtype.ext (face_axis_eval a)]
   exact rides F (Signed.mirror a) ..

def gramC (H : (Model F).Hierarchy) (a : Axis) : (((Model F).Field d)→ₗ⋆[ℂ] ((Model F).Field d) →ₗ[ℂ] ℂ) :=
    LinearMap.comp ((Extra.FD.readsTwo F d (_root_.YM.basis a) 0).flip) ((Model F).adj H.spin d a)

lemma gramC_apply (H : (Model F).Hierarchy)(a:Axis)(x y) : gramC F H (d:=d) a x y=
    (Model F).useAt (Model F) (Extra.FD.couple (_root_.YM.basis a) 0) ![⟨d,y⟩,⟨d,(Model F).adj H.spin d a x⟩] := by
  simp only [gramC,LinearMap.comp_apply,LinearMap.flip_apply]
  have he := Extra.FD.scan_used F d (_root_.YM.basis a) 0 y (((Model F).adj H.spin d a) x)
  convert! he using 1 -- async might timeout via free_model


lemma gramC_pos (H : (Model F).Hierarchy) (a : Axis) {v : (Model F).Field d} (hv:v≠0) : 0 < gramC F H a v v:= by
  change 0 < readsTwo F d (_root_.YM.basis a) 0 v ((Model F).adj (table_spin F) d a v)
  rw [← face_mirror a F, Extra.FD.faceTest_eq]
  exact (Extra.FD.reflected_positive (by intro e; simpa [YM.basis_norm] using! congr_arg norm e) _).mpr (show Extra.FD.writes F d v≠0 from by
    rw [←map_zero (Extra.FD.writes F d)]; exact (Extra.FD.writes_inj F d).ne hv)

def gram (H : (Model F).Hierarchy) (a : Axis): LinearMap.BilinForm ℝ ((Model F).Field d) where
  toFun x := Complex.reCLM.toLinearMap.comp ((gramC F H (d:=d) a x).restrictScalars ℝ)
  map_add' p q:= by
    exact LinearMap.ext fun y=>show (gramC F H a (p+q) y).re=(gramC F H a p y).re+(gramC F H a q y).re by rw [map_add,LinearMap.add_apply,Complex.add_re]
  map_smul' c p := LinearMap.ext fun y=>show (gramC F H a (c•p) y).re=c*(gramC F H a p y).re by
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,LinearMap.smul_apply]
    change ((starRingEnd ℂ (c:ℂ)) * _).re=_
    simp

def transform (H : (Model F).Hierarchy) (s : Signed) := ((Model F).mirror H.spin d s).restrictScalars ℝ

def positive (H : (Model F).Hierarchy):LinearMap.BilinForm ℝ ((Model F).Field d) :=
   ∑ s:Signed, (gram F H (d:=d) 0).comp (transform F H s) (transform F H s)

lemma positive_def (H: (Model F).Hierarchy){v : (Model F).Field d}(h:v≠0):0<positive F H v v:= by
   unfold positive; simp only [LinearMap.sum_apply,LinearMap.BilinForm.comp_apply]
   have he' (s:Signed) : transform F H s⁻¹ (transform F H s v)=v:= by unfold transform; simp only [LinearMap.restrictScalars_apply,←Table.mirror_mul,inv_mul_cancel,Table.mirror_one]
   have he (s:Signed):= gramC_pos F H 0 (show transform (d:=d) F H s v≠0 from fun he=>h (by rw [← he' s, he,map_zero]))
   exact Finset.sum_pos (fun i _=>show _ from (Complex.lt_def.mp (he i)).1) Finset.univ_nonempty

lemma position_invariant (H : (Model F).Hierarchy)(v w : (Model F).Field d) s :
     positive F H ((Model F).mirror H.spin d s v) ((Model F).mirror H.spin d s w)=positive F H v w := by
  unfold positive; simp_rw [LinearMap.sum_apply,LinearMap.BilinForm.comp_apply]
  simp_rw [transform, LinearMap.restrictScalars_apply,← Table.mirror_mul]
  exact Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun _=> rfl)

end Positive
end YM.PertExtension.Rigidity

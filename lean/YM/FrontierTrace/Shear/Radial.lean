import YM.FrontierTrace.Shear.Angular
/-!
Use only off-diagonal stress (spin **not** contracting onto trace). Read the
trace coefficient by a radial conservation identity. Keeping normalization
`r` of operators fixed, one can test it on purity horizon four only with NO
positive-order derivative estimate or multipoint OPE. Specifically only the
order-two with both positions at *two* (or just one difference of) fixed
radii in a generic direction. The ordinary scalar readings on the compact
interval and one weak order zero stress normalization suffice to make this
a well-conditioned system. These analytic inputs are separate from the Ward
identities proved here. Focus centering is the unselected center.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace MeasureTheory Table Climb
open Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (F:Spec.Final C f S)
    (A:S.Field 4)(m:ℝ) (hA : ∀ g:Ortho,F.sector.turns.act 4 g A=A)
local notation "μ0" => timeAxis
local notation "L" => YM.FrontierTrace.currentL F A m
local notation "B" => YM.FrontierTrace.currentB F A m
local notation "T" => YM.FrontierTrace.current F A m

lemma conservation {z:E4}(hz:z≠0) (j:Axis): ∑ i:Axis,D (basis i) (T i j) z=0 := by
   let v:= fun i => F.sector.energy i j
   let w(i:Axis):= F.sector.derivatives.deriv 4 i (m • v i)
   let q:=fun _:Fin 1=> (⟨4,A⟩:S.Tag)
   have he(i:Axis) : D (basis i) (T i j) z = custom (atShape z) (w i) A:=
       D_cons F.room.kernel.smooth _ F.phase.transport.derivatives (m • v i) q (atRoom hz) i
   simp_rw [he]; obtain ⟨K,hK⟩:= custom_linear (e:=5) (atShape z) A
   simp_rw [w,hK, RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,← Finset.smul_sum,← map_sum]
   rw [show ∑ x:Axis, F.sector.derivatives.deriv 4 x (v x)=0 from F.phase.transport.conserved.divergence j,map_zero,smul_zero]

lemma current_diff {z:E4}(hz:z≠0)(i j:Axis): ContDiffAt ℝ ∞ (T i j) z:=
    Work.A01.smooth_cons S F.room.kernel.smooth _ _ (atRoom hz)

lemma slice_diff (t:ℝ) : HasDerivAt slice (basis μ0) t :=by
   simpa only [slice,one_smul] using! (hasDerivAt_id' t).smul_const (basis μ0)

lemma currentD {t:ℝ}(ht:0<t) (i j:Axis): DifferentiableAt ℝ (fun z:ℝ=>T i j (slice z)) t:=
   ((current_diff F A m (slice_nonzero ht) i j).differentiableAt (by simp)).comp t (slice_diff t).differentiableAt

include hA
lemma tilt_derivative (s:ℝ)(hs:0<s){i:Axis}(hi:i≠ μ0):
    D (basis i) (T i μ0) (slice s) = s⁻¹ • B s:=by
   let P (u:E4) := (u μ0 / ‖u‖^2) • B ‖u‖
   have eq : T i μ0 =ᶠ[𝓝 (slice s)] fun u=> u i • P u := by
     filter_upwards [isOpen_ne.mem_nhds (slice_nonzero hs)] with x hx
     have h: 0<‖x‖ := norm_pos_iff.mpr hx
     let p : E4:= ‖x‖⁻¹ • x
     have hp: ‖p‖=1:=by unfold p; rw [norm_smul_of_nonneg (inv_nonneg.mpr h.le), inv_mul_cancel₀ h.ne']
     have he:= slope_angle F A m hA p hp _ h i μ0
     rw [show ‖x‖ • p=x from smul_inv_smul₀ h.ne' x, if_neg hi,zero_add] at he
     dsimp only [P]; rw [he, smul_smul]; apply congr_arg (· • _)
     change (‖x‖⁻¹ * x i) * (‖x‖⁻¹ * x μ0)=_; ring
   have hsn : ‖slice s‖=s:=by simp [slice,norm_smul,Real.norm_eq_abs, abs_of_pos hs]
   have hnorm: DifferentiableAt ℝ (fun u:E4=> ‖u‖) (slice s):= (contDiffAt_norm ℝ (n:=1) (slice_nonzero hs)).differentiableAt one_ne_zero
   let proj:= fun i:Axis=> (EuclideanSpace.proj i:E4→L[ℝ] ℝ)
   have hd : DifferentiableAt ℝ P (slice s):= by
     have hh : DifferentiableAt ℝ B ‖slice s‖ := by
        rw [hsn]; exact DifferentiableAt.sub (currentD F A m hs μ0 μ0) (currentD F A m hs 0 0)
     have hD : DifferentiableAt ℝ (fun x:E4=> x μ0 / ‖x‖^2) (slice s):=by
       have he: ‖slice s‖^ (2:ℕ) ≠ 0:= pow_ne_zero _ (hsn.symm ▸ hs.ne')
       have hv := (hnorm.pow 2).inv he
       simp_rw [div_eq_mul_inv]; exact (proj μ0).differentiableAt.mul hv
     exact hD.smul (hh.comp _ hnorm)
   unfold D; rw [eq.fderiv_eq]
   change (fderiv ℝ (fun y : E4=> proj i y • P y) _) _= _
   rw [fderiv_fun_smul (proj i|>.differentiableAt) hd, (proj i).fderiv]
   simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
   have hz : proj i (slice s)=0:=by change (slice s) i=0; simp [slice,hi]
   have hv : proj i (basis i)=1:=by change basis i i=1; simp
   dsimp only [P]; rw [hz,hv,zero_smul,one_smul]
   rw [zero_add]
   rw [hsn, show (slice s) μ0=s from by simp [slice], show s/s^2=s⁻¹ from by field_simp]

/-- L'+3 B(s)/s=0 with exact stress. -/
theorem ode (s:ℝ)(hs:0<s) : HasDerivAt L ((-(3:ℝ)) • (s⁻¹ • B s)) s := by
   let v : ℂ:= s⁻¹ • B s
   have he:= conservation F A m (slice_nonzero hs) μ0
   have hb : D (basis μ0) (T μ0 μ0) (slice s)= -(3:ℝ) • v:= by
      rw [Fin.sum_univ_four] at he
      rw [tilt_derivative F A m hA s hs (show (0:Axis) ≠ μ0 by decide),
        tilt_derivative F A m hA s hs (show (1:Axis) ≠ μ0 by decide),
        tilt_derivative F A m hA s hs (show (2:Axis) ≠ μ0 by decide)] at he
      rw [neg_smul, eq_neg_iff_add_eq_zero,add_comm, show (3:ℝ) • v=v+v+v by module]; exact he
   have hd := ((current_diff F A m (slice_nonzero hs) μ0 μ0).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (slice_diff s)
   rw [show (fderiv ℝ _ (slice s)) _ = _ from hb] at hd
   exact hd

lemma trace_repaired {t:ℝ}(ht:0<t)(d:ℝ)(h: m • centered F=(4*d) • A)
    (h0:expectation S 4 A=0):
    L t - (3/4:ℝ) • B t = d • custom (atShape (slice t)) A A :=by
   let x:= atShape (slice t); have hx:=atRoom (slice_nonzero ht)
   let Y:= custom x A A
   obtain ⟨K,hK⟩:= custom_linear (e:=4) x A
   have hk : K (m • theta F 0)= K (m • centered F) := by
      have h': K (S.unit 4)=0:=by
         rw [←hK]; exact (unit_left_read F.room.kernel x hx).trans ((expectation_focus A).trans h0)
      simp only [centered,value_center,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_sub,h',smul_zero,sub_zero]
   have he : ((4:ℝ)*d) • Y = ∑ i:Axis, T i i (slice t):= by
      rw [h] at hk
      simp_rw [YM.FrontierTrace.current]
      change _=∑ i:Axis, custom x _ A
      have he : ((4:ℝ)*d) • Y = K ((4*d) • A):=by
         unfold Y; rw [hK]; exact ((K.restrictScalars ℝ).map_smul (4*d) A).symm
      rw [he,← hk,show theta F 0=∑ i:Axis,F.sector.energy i i from by simp [theta,withoutMean], Finset.smul_sum,map_sum]; simp_rw [hK]
   rw [Fin.sum_univ_four, transverse_slice F A m hA t ht 1 (by decide), transverse_slice F A m hA t ht 2 (by decide)] at he
   change ((4:ℝ)*d) • Y=currentS F A m t+currentS F A m t+currentS F A m t+L t at he
   change _=d • Y
   rw [show d • Y=(4:ℝ)⁻¹ • (((4:ℝ)*d) • Y) by module, he]; unfold currentB; module

variable {r:ℝ}
theorem exact_dilation (hr:0<r)(s:ℝ)(hs:0<s)(d:ℝ)(h: m • centered F=(4*d) • A)
    (h0: expectation S 4 A=0):
    HasDerivAt (fun t:ℝ=> t^4 • L (r*t)) ( (4*d*s^3) • custom (atShape (slice (r*s))) A A) s:=by
   let t':= r*s; have hh:0<r*s := mul_pos hr hs
   have hv : HasDerivAt (fun t:ℝ=>L (r*t)) ( (-(3:ℝ)*s⁻¹) • B t') s:=by
     have hD:= (ode F A m hA (r*s) hh).scomp s ((hasDerivAt_id' s).const_mul r)
     apply HasDerivAt.congr_deriv (f':=_) (f:=fun t:ℝ=> L (r*t)) hD
     change ((r*1):ℝ) • ((-(3:ℝ)) • ((r*s)⁻¹ • B (r*s)))= _
     rw [smul_smul,smul_smul]; unfold t'; apply congr_arg (· • B (r*s)); field_simp
   have hq:= trace_repaired F A m hA hh d h h0
   have hK:= ((hasDerivAt_id' s).pow 4).smul hv
   refine hK.congr_deriv ?_
   rw [show 4*d*s^3=(4*s^3)*d by ring,mul_smul (4*s^3) d,←hq]
   unfold t'; norm_num only [Pi.pow_apply, Nat.cast_ofNat,Nat.reduceSub, mul_one]; rw [smul_smul, show (s^4*( -(3:ℝ)*s⁻¹))=(-3)*s^3 from by field_simp]; module
end YM.FrontierTrace

import YM.SchemeRG11.Saddle.Traverse
import YM.Pert.Lattice.Representatives

/-! Absolute Jacobian block helpers. Avoid any compact Lie Haar normalization *assumption*. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.SchemeRG11.Sway
open MeasureTheory Measure Set Metric Function
open scoped ContDiff Topology ENNReal Classical
section block
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
 [NormedAddCommGroup F] [NormedSpace ℝ F] 

def cost (u:E→L[ℝ] E):ℝ:=|ContinuousLinearMap.det u|
lemma cost_com (u v:E→L[ℝ] E):cost (u ∘L v)= cost u* cost v:=by unfold cost; change |LinearMap.det (u.toLinearMap ∘ₗ v.toLinearMap)|=_; exact (congrArg (fun x=>|x|) (LinearMap.det_comp _ _)).trans (abs_mul ..)
lemma cost_id: cost (ContinuousLinearMap.id ℝ E)=1:= by unfold cost; rw [show ContinuousLinearMap.det (ContinuousLinearMap.id ℝ E)=1 from (LinearMap.det_id: LinearMap.det (LinearMap.id (R:=ℝ) (M:=E))=1),abs_one]
lemma cost_conj(e:E≃L[ℝ]F)(u:E→L[ℝ]E): cost (e.toContinuousLinearMap ∘L u ∘L e.symm.toContinuousLinearMap)=cost u:=by unfold cost; apply congrArg _; rw [←ContinuousLinearMap.comp_assoc]; exact LinearMap.det_conj (u.toLinearMap) e.toLinearEquiv
lemma cost_posit (e:E≃L[ℝ]E): 0<cost e.toContinuousLinearMap:= by
 refine abs_pos.mpr ?_; exact (show LinearMap.det e.toLinearEquiv.toLinearMap≠0 from by rw [← LinearEquiv.coe_det];exact Units.ne_zero _)
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma cost_iso (u:E→L[ℝ]E) (hu: cost u ≠ 0): u.IsInvertible:=by
 have hn: LinearMap.det u.toLinearMap ≠0:=fun he=>hu (by unfold cost; rw [show ContinuousLinearMap.det u=0 from he,abs_zero])
 have hi : Injective u.toLinearMap:=LinearMap.ker_eq_bot.mp (by_contra fun h=> hn (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h))
 let e:= (LinearEquiv.ofBijective u.toLinearMap ⟨hi,LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv
 exact ⟨e,rfl⟩
lemma cost_parts(u:E×F→L[ℝ]E×F)(a:E→L[ℝ]E)(b:F→L[ℝ]F)(v:F→L[ℝ]E)(hu:∀ x:E,∀ y:F, u (x,y)=(a x+v y,b y)): cost u = cost a * cost b:=by
 let H:=Module.finBasis ℝ E; let J:=Module.finBasis ℝ F
 let L:=H.prod J
 have he: LinearMap.toMatrix L L u.toLinearMap = Matrix.fromBlocks (LinearMap.toMatrix H H a.toLinearMap) (LinearMap.toMatrix J H v.toLinearMap) 0 (LinearMap.toMatrix J J b.toLinearMap):=by
   unfold L; ext i j; cases i <;> cases j <;> simp [LinearMap.toMatrix_apply,hu]
 have hm : ContinuousLinearMap.det u = a.det*b.det:= by
    change LinearMap.det u.toLinearMap = LinearMap.det a.toLinearMap * LinearMap.det b.toLinearMap
    rw [← LinearMap.det_toMatrix L, he, Matrix.det_fromBlocks_zero₂₁,LinearMap.det_toMatrix,LinearMap.det_toMatrix]
 unfold cost; rw [hm,abs_mul]
lemma cost_up(u:E×F→L[ℝ]E×F)(a:E→L[ℝ]E)(b:F→L[ℝ]F)(hu:∀ x:E, u (x,(0:F))=(a x,0))(hv:∀ y:F,(u (0,y)).2=b y):cost u=cost a*cost b:=by
 apply cost_parts u a b ((ContinuousLinearMap.fst ℝ _ _).comp (u.comp (ContinuousLinearMap.inr ℝ _ _)))
 intro x y
 rw [show (x,y)=(x,(0:F))+(0,y) by simp,map_add,hu]
 apply Prod.ext
 · rfl
 change 0+(u (0,y)).2=b y;rw [hv,zero_add]
lemma cost_down(u:E×F→L[ℝ]E×F)(a:E→L[ℝ]E)(b:F→L[ℝ]F)(hu:∀ x:E,(u (x,(0:F))).1=a x)(hv:∀ y:F,u (0,y)=(0,b y)):cost u=cost a*cost b:=by
 let e:=ContinuousLinearEquiv.prodComm ℝ E F
 let w:= e.toContinuousLinearMap ∘L u ∘L e.symm.toContinuousLinearMap
 have h(y:F): w (y,(0:E))=(b y,0):=by change Prod.swap (u (0,y))=_; rw [hv];rfl
 rw [← cost_conj e u,cost_up w b a h (fun y=>hu y),mul_comm]
lemma cost_norm(u:E→L[ℝ]E)(hu:∀ a, ‖u a‖=‖a‖):cost u=1:=by
 letI : MeasurableSpace E := borel E
 letI : BorelSpace E:= ⟨rfl⟩
 let μ := (Module.finBasis ℝ E).addHaar
 let e:=ball (0:E) 1
 have hi : μ e ≠ 0:= (isOpen_ball.measure_pos μ ⟨_,mem_ball_self zero_lt_one⟩).ne'
 have hj : μ e ≠ ⊤ := (isBounded_ball.measure_lt_top).ne
 have hs : Surjective u:=LinearMap.surjective_of_injective (f:=u.toLinearMap) (fun i j h=> dist_eq_zero.mp (by rw [dist_eq_norm_sub,← hu (i-j),map_sub,sub_eq_zero.mpr (show u i=u j from h),norm_zero]))
 have he: u '' e=e:=by
    apply Subset.antisymm ?_ ?_
    · rintro _ ⟨x,hx,rfl⟩; simpa [e,hu] using (show ‖x‖<1 from by simpa [e] using hx)
    intro y hy; obtain ⟨x,hx⟩:=hs y; refine ⟨x,?_,hx⟩
    rw [← hx] at hy; simpa [e,hu] using hy
 have hx: (μ e)= ENNReal.ofReal (cost u) * (μ e):=by nth_rw 1 [← he]; exact addHaar_image_continuousLinearMap μ u e
 have he: ENNReal.ofReal (cost u)=1:=by
    exact ENNReal.mul_left_inj hi hj |>.mp (show ENNReal.ofReal (cost u)*_=1*(μ e) from hx.symm.trans (one_mul _).symm)
 simpa [cost] using congr_arg ENNReal.toReal he
end block
section field
open Lattice PertExtension.Orb Pert.Orb
variable {n:Side}{G:Gauge}
abbrev drift (t:G.El): G.Color→L[ℝ]G.Color:=(G.adjoint t).toContinuousLinearMap
lemma cost_drift(t:G.El):cost (drift t)=1:=cost_norm _ <| G.norm_adjoint _
end field
end YM.SchemeRG11.Sway

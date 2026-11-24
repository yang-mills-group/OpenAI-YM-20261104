import YM.OPE.Compatible.Rail.Mews
import YM.Push.FREE_RESOLVENT.Test
/-! # Flat Means rollout -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Asymptotics Work.F05 Stationary
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type*} {G:Gauge}{c f:Side}{S:StepData c f} {p q:Clip}{R T:PathData G} {F:Tree.Forest S.ratio} {a b e y d m Λ:ℝ} {B C':Bed}
namespace Virgin
local notation "C" => (Bid.Dir G c)
local notation "P"=>AxisChart G F
abbrev verge (F:Forest S.ratio) (t:S.Choices)(p:Clip)(R:PathData G):=score F t p R
lemma basing (t:S.Choices)(p:Clip)(R:PathData G): tested F t p R 0 = verge F t p R 0:=by
    funext i; unfold tested verge score lifting fieldF; simp only [link_one, replica_one, Pi.one_apply, mul_one]
lemma frozen {F:Forest S.ratio}(t:S.Choices){g:C→AxisChart G F}(h:Critical F p R g)(hx:Bid.Comptroller F B p R): damage (countingBasis F G) (verge F t p R 0) 0=FreeResolvent.treeMatrix G S F B.metric:=by
    rw [← basing]; exact (hessian_eq ..).symm.trans (FreeResolvent.Tests.checked_loop F B t p R (fun i=>(h.2.2 i).1) hx)
lemma oneRay (x:C):HasDerivAt (fun i:ℝ=>i•x) x 0:=by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x
lemma thumb (F: Forest S.ratio)(t:S.Choices){g:C→AxisChart G F}{A:Matrix (Body 1 f) (Body 1 c) ℝ}(h: Critical F p R g)(hp: Guessed F A g)(v:C)(i:F.Free):
   fderiv ℝ (cabin g) 0 v i= relative F A v i + linearCopy S.ratio (collect G v) i:=by
      have hz: (0:ℝ) • v=0:= zero_smul ..
      have ha:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : F.Free=>G.Color) i).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hp v)
      let U(a:ℝ):= exposure F (a • v) (g (a • v)) i; have ht:U 0=1:= by unfold U; rw [hz,h.1,exposure_zero]; rfl
      have hY:HasDerivAt (fun x=> G.mat (U x)) (G.colorMat (relative F A v i+linearCopy S.ratio (collect G v) i) * G.mat (U 0)) 0:=by
         have h1: HasDerivAt (fun a:ℝ=>G.mat (G.lieExp (g (a • v) i))) (G.colorMat (relative F A v i)) 0:= by
            have he : HasFDerivAt (fun x=>G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap (g ((0:ℝ) • v) i):=by rw [hz,h.1,Pi.zero_apply]; exact G.expDiff_zero
            exact he.comp_hasDerivAt _ ha
         have h2: HasDerivAt (fun a:ℝ=>G.mat (replica S.ratio (represent (a • v)) i)) (G.colorMat (linearCopy S.ratio (collect G v) i)) 0:=by
            unfold replica linearCopy; split; rw [map_zero]; exact hasDerivAt_const ..
            exact Work.F03.represent_rate v (S.ratio.parent i.val.1,i.val.2)
         rw [ht]; simp_rw [U,exposure,G.mat_mul]; convert! h1.mul h2 using 1; simp only [hz,h.1,Pi.zero_apply,G.mat_lieExp_zero,link_one,replica_one,G.mat_one,one_mul,mul_one,Pi.one_apply,map_add]
      have he: HasDerivAt (fun a:ℝ=> cabin g (a • v) i) (relative F A v i + linearCopy S.ratio (collect G v) i) 0 := by
         have hr:=Push.Loops.delta_rate (v:=U) hY; rw [ht] at hr; simpa only [Push.Loops.delta,inv_one,mul_one] using! hr
      have hh : HasFDerivAt (cabin g) (fderiv ℝ (cabin g) 0) ((0:ℝ) • v):= hz.symm ▸ ((solvedPath h t).2.1.differentiableAt (by simp)).hasFDerivAt
      have hv:= hh.comp_hasDerivAt (l:=cabin g) (0:ℝ) (oneRay v); have hy:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : F.Free=>G.Color) i).hasFDerivAt.comp_hasDerivAt (0:ℝ) hv; exact hy.unique he
open FreeResolvent
lemma plantT (t:S.Choices){g:C→P}{A:Matrix (Body 1 f) (Body 1 c) ℝ}(h:Critical F p R g)(hp:Guessed F A g)(v:C)(i:Active G F): cash (countingBasis F G) (fderiv ℝ (cabin g) 0 v) i=(tensor G (extracted S F A)*ᵥ flatten v) (plant F i):=by
     rw [rangers_fee, thumb F t h hp]; change (((extracted S F A*ᵥ parts G 1 v i.2) _ -_)+ linearCopy S.ratio (collect G v) i.1 i.2) = component (tensor G _ *ᵥ _) i.2 _; rw [sub_add_cancel,component_mul]; rfl
lemma receives {g:C→P}{T:Towers S.patch.L}(h:Critical F p R g)(ht:0<e)(hL:Bid.Larger (G:=G) S)(hg:Towers.Diagonal S B C' T)(he: Floor B p f e y)(hh: Floor C' q c a b)(hy:R.Bounds p d m Λ)(hr:Attached B R)(hv:Bid.Sworn B f G): Guessed F (installed S.ratio T.A0) g :=by
    obtain ⟨η,hη,H⟩:= (Bid.cospons Work.E02.answer Work.F01.answer Work.F02.answer Work.F03.answer Work.F04.answer S.patch.L S.patch.J S.kernel e ht (G:=G)).χ; obtain ⟨hP,X,hX,hA,hx⟩:= H _ _ S rfl rfl rfl hL F B C' p q R d m Λ y a b _ hg he hy hr hv hh
    let t:=Classical.arbitrary S.Choices; have he : g=ᶠ[𝓝 0] X:= by
        refine station_unique (F:=tested F t p R) (h.2.2 t).1 ?_ (h.1 ▸ h.2.1.continuousAt.tendsto) (hX.1 ▸ hX.2.1.continuousAt.tendsto) ((h.2.2 t).2.mono fun i hi=>hi.fderiv) ((hX.2.2 t).2.mono fun i hi=>hi.fderiv); intro y hy; exact Classical.byContradiction fun hh=> (tested_diag hη hP t _ hh).ne' hy
    intro x; refine (hA x).congr_of_eventuallyEq ?_; refine Tendsto.eventually ?_ he; simpa using (oneRay x).continuousAt.tendsto -- fdef
end Virgin
end YM.OPE.Flume

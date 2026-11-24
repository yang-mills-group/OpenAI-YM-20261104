import YM.SchemeConversionRG11.FirstW.Jade.Export
import YM.Pert.Triangle.ShellFan
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge}{T: Itinerary} {n:Side} {W:Axis → Axis → G.Color}
def door (W:Axis→Axis→ G.Color) : Bare.Response G 0:= fun i j _=>W i j
lemma radial0 {Q:TwoJet G.Color 0}(h:∀ i j,Q i j = -Q j i): Q∈onShell G.Color 0 := by
 have he(i j:Axis): diagonal (Q i j) =fun _=> Q i j 0:= funext fun x=>congrArg (Q i j) (Subsingleton.elim (fun _:Fin 0=>x) 0) -- may subsingleton
 have hp(i j k:Axis): grad k (diagonal (Q i j))=0 := by rw [he]; funext x; unfold grad Analysis.D; simp
 refine ⟨⟨fun i j r s=>congrArg _ (Subsingleton.elim ..),h,fun i j k x=>?_⟩,fun b x=>?_⟩ <;> simp [hp]
lemma door_own (h:∀ i j,W i j= -W j i): ∃ S: Shell G 0,door W=Bare.components (gaugeJet S):= by
 let Q :TwoJet G.Color 0:= fun i j=> Bare.spaceMon (fun i:Fin 0=> i.elim0) (W i j)
 let e(i j:Axis)(x:Fin 0→E4): Q i j x = W i j:= by unfold Q; rw [Bare.mon_eq]; simp
 have hh: Q∈onShell G.Color 0:= radial0 (fun i j=> ContinuousMultilinearMap.ext (fun x=>by rw [e]; simp only [neg_apply];rw [e,h i j]))
 refine ⟨⟨Q,hh⟩,?_⟩; funext i j γ; rw [Bare.components,match_leg]; exact (e ..).symm
open Push.FiniteDetection.Free.Hyper hiding turn pull flip
lemma radial_view (W:Axis→Axis→G.Color)(h:∀ i j,W i j=-W j i)(s:Signed): Labels.Taylor.turn s.ortho (Bare.radialMap (door (fun i j=> (violet s i * violet s j) • W (s.perm i) (s.perm j))))=Bare.radialMap (door W):=by
 obtain ⟨Q,H⟩:=door_own h; let X:=Push.FiniteDetection.Free.Hyper.turn s Q
 have he : door (fun i j=> (violet s i*violet s j) • W (s.perm i) (s.perm j))= Bare.components (gaugeJet X):= by
   funext i j γ
   have hm : W (s.perm i) (s.perm j)= Q.val (s.perm i) (s.perm j) (fun u=> basis (γ u)):= by
      unfold door Bare.components at H; simp only [match_leg] at H; exact congrFun (congrFun (congrFun H (s.perm i)) (s.perm j)) _
   rw [door,Bare.components, match_leg,hm]; change _=(violet s i * violet s j) • Q.val (s.perm i) (s.perm j) _; apply congrArg _; exact congrArg _ (Subsingleton.elim ..)
 simp only [he,H]; rw [show Bare.radialMap (Bare.components (gaugeJet X))= gaugeJet X from Bare.complete _,show gaugeJet X= _ from gaugeTurn s Q, ← Labels.Taylor.turn_mul,mul_inv_cancel]; simp; exact (Bare.complete (gaugeJet Q)).symm
lemma vector_at (W:Axis→Axis→G.Color)(h:∀ i j,W i j= -W j i)(b:Bool)(i:Fin 3): fanReading b i (Bare.radialMap (door W))=(2:ℝ)⁻¹ • ∑ a:Axis,∑ c:Axis, fan b i a c • W a c:= by
 have ht: Bare.components (Bare.radialMap (door W))=door W:= by obtain ⟨Q,e⟩:= door_own h; rw [e,show Bare.radialMap _=gaugeJet Q from Bare.complete _]
 have h (a c:Axis): UVNext.FreeStress.component (UVNext.FreeStress.initialPlace a c) (Bare.radialMap (door W))= W a c := by
   have H:=congrFun (congrFun (congrFun ht a) c) (fun i:Fin 0=> i.elim0); unfold Bare.components at H; change Maxwell.takeCurl _ _ _ _ =W a c; apply Eq.trans ?_ H; apply congrArg _; exact Subsingleton.elim ..
 simp only [fanReading, LinearMap.smul_apply,LinearMap.sum_apply,h]
end YM.RG11.FirstW

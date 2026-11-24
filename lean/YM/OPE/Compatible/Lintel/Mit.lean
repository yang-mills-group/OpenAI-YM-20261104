import YM.OPE.Compatible.Lintel.Wafer
/-! # Thermal equality on repeat axes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
variable (S)(hr:Odd S.ratio.count.val) (X:Boxes G S.patch S.kernel)
local notation "F"=>forest S.ratio hr
lemma hearing (t:S.Choices){g:Bid.Dir G c→AxisChart G F}{L:Matrix (Body 1 f) (Body 1 c) ℝ}{B: Bed}(h:licensed S hr X p R L B g)(he:R.Bounds p s u b)(hp: LocalRatio V)(hx:FiniteBound F R T p q α V g T₁ T₂ b')(v:Bid.Dir G c):iteratedFDeriv ℝ 2 (thermal F t p R g V) 0 ![v,v]= X.silo R p V c ![spool G c v, spool G c v]:=by
    let A:=pane F t p R; let D:=cabin g; let M:=FUND S hr X; let K:= countingBasis F G; have hM:=ulk_force S hr X; let P:= dance S hr G; let w:=fieldT D v; let u':=fieldU D v v; have hh:=dawn S hr X t h he; have ht:(M⁻¹).IsSymm:=by have he := hM.inv.isHermitian.eq; simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using he
    have hf: tuneH X.dot (voteV S.patch S.kernel R p 3) (voteV S.patch S.kernel R p 4) c ![P w,P w]=heatPay A K M⁻¹ w w u':=by
        let x:=X.dot; let T:= ROOT (I:=Shade G) x; let y:= voteV S.patch S.kernel R p 3; let Y:= voteV S.patch S.kernel R p 4; have hY:Summable y:=folk_whole (folkS (penne_unit R p S.patch S.kernel he 3) _); unfold tuneH
        have ht1: -cityTap (T.acts c) (cotton T y y) ![P w, P w]=(M⁻¹*HATCH A K u').trace:= hh.ringQ v X.rocket1 hY
        have ht2: cityTap (T.acts c) Y ![P w,P w]=(M⁻¹*ROACH A K w w).trace:= hh.lineU (vote_here S hr h.1.cover t p R he 4) w
        have ht3: cityTap (T.acts c) (swing (Equiv.swap (1:Fin 4) 2) (cotton T y y)) ![P w,P w]= _ := hh.tapDouble w X.rocket1 hY ht
        dsimp only; erw [ht1,ht2,ht3]; rfl
    have hg : damage K (score F t p R 0) 0=M:=by erw [frozen t h.2.1 h.2.2.2, h.1.metric]
    rw [luxury t h.2.1 hg hM.det_pos.ne' he hx hp v v]; unfold Boxes.silo; erw [show (fun i=> X.main.acts c *ᵥ ![spool G c v,spool G c v] i)= ![P w,P w] from funext fun i:Fin 2=>by fin_cases i <;> exact (Script.bounty S hr X t h v).symm]; obtain ⟨hC,hB⟩:=marchY S hr hp he w; unfold Boxes.tuneP; erw [hC, hf,hB]; ring -- maybe change let
end Script
end YM.OPE.Flume

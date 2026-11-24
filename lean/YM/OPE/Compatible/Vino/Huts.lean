import YM.OPE.Compatible.Vino.Shack
/-!
# response through sorted frame
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l:ℕ}
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ}
variable (P:Patch)(C:KernelChoices) (U:Boxes G P C) (A:Alps K T i v) (V:ChartRatio G)
variable (S:StepData c f)(he:Odd S.ratio.count.val) (t:S.Choices)(Z:Boxes G S.patch S.kernel)
local notation "X!"=> forest S.ratio he
local notation "Y!"=> AxisChart G X!
variable (g:Bid.Dir G c→AxisChart G (forest S.ratio he))
variable (p:Site c)(x:Bid.Dir G c)(Y:FibreRep S he Z t (i:=i) A g b)
-- principle unit Tel damp. impulse `Power` in rank x+w with upstream possible >budget Wick.
abbrev dressedF (u:Bid.Dir G c)(y:Y!):= ribz S he (Fiber.drape (Libra.Keys G (Body 1 c)) Y! Y.L.M (u,y))
lemma helmQ (w:ℝ)(W:Curtain (Shade G))(l:Phase)(r:ℕ)(d:ℕ)(h:Volume W (d+l.val) r w)(ht:LocalRatio V):
     let y(i:Y!):= Flair W (d+l.val) (spool G f (dressedF A S he t Z g Y x i)) (S.ratio.embed p)
     let T:=TracePay S he Z A t g V d (impulse l W) _ p Y x
     (∀ j:Phase,j<l→T.seq j.val=0) ∧ T.seq l.val=Y.L.Q.average (Chart.tangent G (forest S.ratio he).Free) y:=by
          intro y T
          let D:=impulse l W;let V':= Flash A V S he t Z g x Y; let s:Y!→Token:=fun i=>JetS.plainJ (y i)
          have hp:ScriptJ.B s:=by
               have hh: ScriptJ.B (bitH A S he t Z g p x Y (impulse l W) d):= bitB _ _ _ _ _ _ _ _ _ _ (nip _ _ _ _ _ h)
               apply Shell.sty; convert! hh l.val using 1; funext i; change y i=(inkM _ _ _ _).seq _; rw [impBox W d l (dressedF A S he t Z g Y x i)]; fin_cases l<;>norm_num [Ū,JetS.plainJ,JetS.seq,pow_succ] <;> rfl
          let R:=Y.L.Q; let m:=Chart.tangent G (forest S.ratio he).Free; have hT : T= Ū^l.val* fair m R V' s:=by
               unfold T; rw [timely]; let s' (i:Y!):= Ū^l.val * s i
               rw [show bitH A S he t Z g p x Y (impulse l W) d=s' from funext fun i=> impBox ..]; exact coin_F m R _ _ _ hp (flared A V S he t Z g x Y ht)
          rw [hT]; have hv(i:Y!): (V' i).s=1:= Adhesion.curT (Y.L.signPay ht) _ -- polarity
          have ht: (draw V' R m).s=1:=by change R.average m _= _; rw [show (fun v:Y! =>(V' v).s)=(fun _=>1) from funext hv]; exact singleConst ..
          have hh: (fair m R V' s).s= R.average m y:=by
               unfold fair; simp only [JetS.dv,JetS.ml_s, JetS.sp_s,ht, inv_one,mul_one]; unfold draw; dsimp only; simp only [Pi.mul_apply,JetS.ml_s,hv,mul_one];rfl
          refine ⟨fun j hj=>?_,?_⟩
          · revert hj; fin_cases j <;> fin_cases l <;> simp [Ū,pow_succ,JetS.seq]
          fin_cases l <;> norm_num [Ū,pow_succ,JetS.seq]; all_goals exact hh
end YM.OPE.Cascade.Paver

import YM.OPE.Compatible.Vino.Sam
/-!
# τ‐ Salary localized. Exact linearity and tier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m:ℕ}
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ}
variable (P:Patch)(C:KernelChoices) (U:Boxes G P C) (A:Alps K T i v) (V:ChartRatio G)
variable (S:StepData c f)(he:Odd S.ratio.count.val) (t:S.Choices)(Z:Boxes G S.patch S.kernel)
local notation "X!"=> forest S.ratio he
variable (g:Bid.Dir G c→AxisChart G (forest S.ratio he))
variable (p:Site c)(x:Bid.Dir G c)(Y:FibreRep S he Z t (i:=i) A g b)
variable {F E:Type}
section costs
lemma vein_i (X:Muse G)(d:ℕ)(p:Site n)(x:Bid.Dir G n)(i:Phase): (inkM X d p x).seq i.val= Flair (X i) (d+i.val) (spool G n x) p:=by fin_cases i<;>rfl
abbrev bitH (W:Muse G)(d:ℕ)(q:AxisChart G X!) := inkM W d (S.ratio.embed p) (ribz S he (Fiber.drape (Libra.Keys G (Body 1 c)) (AxisChart G X!) Y.L.M (x,q)))
lemma bitB (W:Muse G){b:ℝ}(hp:Tide W d m b): ScriptJ.B (bitH A S he t Z g p x Y W d):=by
      let F:= Fiber.drape (Libra.Keys G (Body 1 c)) (AxisChart G X!) Y.L.M; let V:= ribz S he ∘L F.toContinuousLinearMap; exact fun i=> Shift.leanB _ (((meridian W d m _ _ hp) i).compLinear V.toLinearMap) x -- application b shadow
abbrev Flash (q:AxisChart G X!):= Y.L.cloth V (x,q)
lemma flared (h:LocalRatio V): ScriptJ.B (Flash A V S he t Z g x Y):= fun i=> Shift.leanB _ (Fiber.cloth_B (F:=Y.L) h i) x
lemma timely (W:Muse G)(d:ℕ) : TracePay S he Z A t g V d W _ p Y x= fair (Chart.tangent G (forest S.ratio he).Free) Y.L.Q (Flash A V S he t Z g x Y) (bitH A S he t Z g p x Y W d) :=rfl
lemma Ink_sum (p:Site n)(t:Bid.Dir G n)(X Y:Muse G)(d:ℕ)(a b:ℝ) (hx:Tide X d m a) (hy:Tide Y d m b): inkM (X+Y) d p t=inkM X d p t+inkM Y d p t:=by apply JetS.eta; exact flairA _ _ _ ((hx 0).bound _) ((hy 0).bound _); exact flairA _ _ _ ((hx 1).bound _) ((hy 1).bound _); exact flairA _ _ _ ((hx 2).bound _) ((hy 2).bound _)
lemma Ink_scale (p:Site n)(t:Bid.Dir G n)(X:Muse G)(c:ℝ)(d): inkM (c • X) d p t= JetS.plainJ c * inkM X d p t:=by
     have hp(i:Phase): Flair (c • X i) (d+i.val) (spool G n t) p= c* Flair (X i) (d+i.val) (spool G n t) p:=by unfold Flair Flume.Script.value; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [Pi.smul_apply,score_scaled]
     apply JetS.eta
     · exact hp 0
     · change Flair _ _ _ _= c * _ + 0*_; rw [zero_mul,add_zero]; exact hp 1
     change Flair _ _ _ _= c *_+0*_+0*_; rw [zero_mul,zero_mul,add_zero,add_zero]; exact hp 2
lemma jetSum (W D:Muse G)(a b:ℝ)(hW:Tide W d m a)(hD:Tide D d m b)(hr:LocalRatio V): TracePay S he Z A t g V d (W+D) _ p Y x=TracePay S he Z A t g V d W _ p Y x+TracePay S he Z A t g V d D _ p Y x:=by simp_rw [timely]; let B:=bitH A S he t Z g p x Y; rw [show bitH A S he t Z g p x Y (W+D) d=B W d+B D d from funext fun z=> Ink_sum _ _ _ _ _ _ _ hW hD]; exact Firmly _ _ _ (flared A V S he t Z g x Y hr) (bitB A S he t Z g p x Y W hW) (bitB A S he t Z g p x Y D hD)
lemma jetL (W:Muse G)(a c:ℝ)(hW:Tide W d m a)(hr:LocalRatio V): TracePay S he Z A t g V d (c • W) _ p Y x=JetS.plainJ c * TracePay S he Z A t g V d W _ p Y x:=by simp_rw [timely]; let B:=bitH A S he t Z g p x Y; rw [show bitH A S he t Z g p x Y (c • W) d= fun i=> JetS.plainJ c*B W d i from funext fun i=>Ink_scale ..]; exact coin_F _ _ _ _ _ (bitB A S he t Z g p x Y W hW) (flared A V S he t Z g x Y hr)
end costs
end YM.OPE.Cascade.Paver

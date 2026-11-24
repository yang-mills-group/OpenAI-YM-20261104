import YM.OPE.Compatible.Grafts.Espy
/-!
# Ordinary and quotient paths. Poles
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)
local notation "X!"=> forest S.ratio he
local notation "Z!" => AxisChart G X!
local notation "K!" => Bid.Dir G c
local notation "U!" => Bid.Dir G f
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable {P:ChartRatio G}(ht:LocalRatio P)
open Flume.Script Shell Char Pilot
open Planned.PrimaryIntegral295.Carrier
variable (n c:Side)
def trimT (h:c.val∣n.val): Site n→+ Site c :=AddMonoidHom.pi fun i=> (ZMod.castHom h (Per c)).toAddMonoidHom.comp <| Pi.evalAddMonoidHom (fun _:Axis=> Per n) i
variable {n c}
variable (hd:c.val∣n.val)
local notation "Ψ"=> trimT n c hd
lemma lease (x:Cover): Ψ (wrap n x)=wrap c x:=by funext i; exact map_intCast (ZMod.castHom hd (Per c)) _
def pushB : Body 1 n→ Body 1 c:= fun i=> (trimT n c hd i.1,i.2)
def Booklet (G:Gauge) : Bid.Dir G c→L[ℝ] Bid.Dir G n:= ContinuousLinearMap.pi fun i=>ContinuousLinearMap.proj (pushB hd i)
local notation "W"=> Booklet hd G
lemma labRel (p:Site n)(x:Bid.Dir G c)(d:ℕ)(q:Muse G) : inkM q d p (W x)= inkM q d (Ψ p) x:=by
     have hv(k:ℕ)(Q:Curtain (Shade G)): Flair Q k (spool G n (W x)) p= Flair Q k (spool G c x) (Ψ p):= by
          unfold Flair Flume.Script.value scribe; apply Finset.sum_congr rfl; intro i _; refine tsum_congr (fun b=>congr_arg (Q i b*·) ?_); apply Finset.prod_congr rfl; intro j _; change spool G c x (Ψ (p+wrap n (b j).1),(b j).2) = _; rw [map_add,lease]
     apply JetS.eta <;> exact hv _ _
lemma book_eq (p:Bid.Dir G c) : ‖spool G n (W p)‖ ≤ ‖spool G c p‖:=by apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; exact norm_le_pi_norm (spool G c p) (Ψ i.1,i.2)
lemma brink {a₁ a₂:ℝ→ Bid.Dir G c} {q:ℝ→Site c→G.El}(h:(tor c).Track a₁ a₂ q): (tor n).Track (W ∘ a₁) (W ∘ a₂) (fun x=> q x∘ Ψ):=by
     let P:= Booklet hd G; refine ⟨P.contDiff.contDiffAt.comp _ h.hX, P.contDiff.contDiffAt.comp _ h.hY, ?_, ?_,?_, fun i=> h.chart _⟩; rw [Function.comp_apply,h.gx,map_zero]; rw [Function.comp_apply,h.gy,map_zero]
     filter_upwards [h.law] with i hi; funext p; unfold Score.dress tor; let k:=axisEquiv.symm p.2; change q i (Ψ p.1)* put _ (Ψ p.1,p.2)*(q i (Ψ (p.1+step k)))⁻¹= put _ (Ψ p.1,p.2); rw [map_add,show Ψ (step k)=step k from by rw [← wrap_step,lease,wrap_step]]; exact congr_fun hi (Ψ p.1,p.2)
-- eventual of licence
end YM.OPE.Cascade.Rill

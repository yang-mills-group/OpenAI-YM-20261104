import YM.OPE.Compatible.Sward.Blossom
/-!
# The sunlight criterion, arbitrary competent launches. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {U:Boxes G P K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
open JetS
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}
variable {B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)
open Phere Silt.Phere -- namespace not open? after
namespace Topic
variable (Z:Topic H hs X B D₀)
def Stone (Y:M→ℝ)(U:Z.Ω M Y):Prop:=∀ i:M, ∀ p:Tracts G d τ, ratios p (l+1)→ p∈ U.flag (l+1) i
local notation "S!"=> Sailing T P p R b
lemma marchQ (V:S!)(p:Tracts G d τ)(hv:ratios p j)(i:ℕ): ratios (Quoin hs D₀ B H V i p) j:= by
       let U:= V.U i; let A:=V.U (i+1); let E:=ship P U.gear; have hp:A.gear=E.land:=interlock P _ _ (V.shot i); have hh:Town U A (charmSeal B U.gear) R (V.fare i) := cuplet H B i; exact matelot H E U A B D₀.aware ⟨P.order_cut,P.order_cut,Or.inl rfl⟩ rfl p hp hs hh hv
lemma finalRound (x:T!)(h:ratios x (l+1))(a:Phase): x a∈ (Drift.Turns D₀ a).flag (l+1):=by
        have he:l<τ a:= sternCap D₀ _; let u:=d+a.val; rw [show (Drift.Turns D₀ a).flag (l+1)=fillet G (d+a.val) _ (l+1) (by omega) from (by simp [Drift.Turns,tuneG])]; refine (decrement (x a)).2 (fun i b u hv=>?_); have ht:i< l+1:=(by omega); simp only [h a i (by omega),sliceP,Pi.zero_apply,well,zero_mul,tsum_zero]
lemma budK :Stone Z (Sailing.cost) Z.Wb:=by -- arguments order
       intro i x hx; let L:=Quoin hs D₀ B H i; rw [show Z.Wb.flag (l+1) i = Lingo (Z.t l) L from habitats Z.r Z.t Z.bill (Nat.lt_succ_self l) i]; let f:=race L 0 x; have hh(j):ratios (f j) (l+1):=by
               induction j with
               | zero=> exact hx
               | succ j ih=> rw [show f (j+1) =L j (f j) from by unfold f; rw[gait,Pi.zero_apply,add_zero]]; exact marchQ i _ ih j
       let V:= Z.bill l (by omega); obtain ⟨c,hc,hC⟩:= (V.Yi.1); exact ser (T:=Drift.Turns D₀) L (fun n=> (V.HP _ _)) f (propel L x) ((V.chip 0).Fast) (hC i) (fun a n=> finalRound _ (hh n) a)
end Topic
end YM.OPE.Stroke

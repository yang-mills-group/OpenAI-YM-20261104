import YM.OPE.Compatible.Kyoto.Clock
import YM.OPE.Compatible.Kyoto.Room
/-!
# Rate and diagonal estimates for frame transport

`Adventure` is the frame transport on the finite-dimensional blocks
of dimensions `dims`. Under the input rate bounds, `FortuneW` bounds
its upper exponential rate by zero. When the two scale parameters
differ by `Δfare` and the step satisfies the hypotheses of `ΡbFly`,
the transport eventually satisfies the diagonal bounds in `Flyer`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial
section
variable {L:PriceBook H T}{a:Axis}
variable (V:Foyer L hs a l d)
local notation "vP"=> V.pay
local notation "Z!"=> V.pay.st
set_option quotPrecheck false
local notation "E!"=> Eagle (Z!).Glp (Z!).Z a (vP).policy
noncomputable abbrev dims (V:Foyer L hs a l d) : Fin (l+1)→ℕ:=fun i=> Module.finrank ℝ (Link V.pay.st.Glp V.pay.st.Z a V.pay.policy i)
local notation "p!"=> (Z!).S
open Lake(Flyer Treaty)
noncomputable abbrev Νu := Classical.choose (SigmaFares (Z!).Glp (Z!).Z a (vP).policy)
lemma FruS:1≤ Νu V∧ChargeP (dims V) (p!).L (ΦAct (Z!).Glp (Z!).Z a (vP).policy) (Νu V):=Classical.choose_spec (SigmaFares (Z!).Glp (Z!).Z a (vP).policy)
abbrev Δfare (G:Gauge)(n:Side):= G.slopeConstant*Real.log (n.val:ℝ)
private lemma hi_S (hp:1<n.val) (h:G.Simple): 0< Δfare G n:= mul_pos (Gauge.slopeConstant_pos h) (Real.log_pos (by exact_mod_cast hp))
lemma πBit :∃ D:ℕ, Νu V*2 < Δfare G (p!).L *D/2 := by
        let L:=(p!).L; let v:= Δfare G L; have he: 0 < v:= hi_S (show 1<L.val from Nat.lt_of_lt_of_le (by decide : 1<3) (p!).coarse) hs; let x:= Νu V; obtain ⟨i,hi⟩:=exists_nat_gt (2*x*2/v); use i; have hi':2*x*2< i*v:=(div_lt_iff₀ he).mp hi; linarith only [hi']
noncomputable abbrev κBit := Classical.choose (πBit V)
lemma αBit (hb:n=(p!).L^m)(hn:3≤n.val) : m* Νu V*2 < Δfare G n*(κBit V)/2:=by
        let Q:= (p!); have hc : (0:ℝ)<↑m:=Nat.cast_pos.mpr (by contrapose! hn; rw [show n=1 from (hb.trans (by rw [Nat.eq_zero_of_le_zero hn,pow_zero]))];exact (by decide)); have he :Δfare G n=m*Δfare G Q.L:=by unfold Δfare; rw[hb]; push_cast; rw[Real.log_pow]; ring
        rw [he]; linarith only [mul_lt_mul_of_pos_left (Classical.choose_spec (πBit V)) hc]
variable {p q:Clip}{he:highStage L hs a V≤ i}{hp:highStage L hs a V≤ j}
variable (X:BankW L hs a V he p)(Y:BankW L hs a V hp q)
variable (f:I→Cab T i p)(g:I→Cab T j q)
local notation "τ!"=>Tracts G d (Z!).τ
variable {l₀:Filter I}{Bf Bc ε c:I→ℝ} {W:Side}
variable (S:I→Tracts G d V.pay.st.τ→L[ℝ] Tracts G d V.pay.st.τ)
local notation "ψ"=> fun i=>EFrame X.cart (f i) Y.cart (g i) (S i)
noncomputable abbrev Adventure (W:Side)(s:τ!→L[ℝ] τ!)(b:Cab T i p)(d:Cab T j q)(c:ℝ):= FeeF (dims V) (τΡ X.cart b Y.cart d s c) W
variable (hT:Tendsto c l₀ atTop)(hx:RateLE l₀ c (fun i=> (f i).fees) 0)(hy:RateLE l₀ c (fun i=>(g i).fees) 0) (hr:RateLE l₀ c S 0)(hz:RateLE l₀ c ε (-(1/2)))
include hT hx hy hr hz
lemma FortuneW : RateLE l₀ c (fun i=> Adventure V X Y W (S i) (f i) (g i) (ε i)) 0:= borderW _ (ψ) hT (Uclock X.cart f g Y.cart S hT hx hy hr) hz
variable (hb:W=V.pay.st.S.L^m)(hn:3≤W.val)(hα:∀ᶠ v in l₀,Ace V.pay.st.stars H hs a ((f v).ℳ) ((g v).ℳ) (zero_le_one.trans (f _).positive) (zero_le_one.trans (g v).positive) (V.pay.st.S.order_cut.trans he) (V.pay.st.S.order_cut.trans hp) m (S v)) (he0: Tendsto Bf l₀ atTop) (hB:RateLE l₀ c Bf 1)(hL:∀ᶠ i in l₀,Bf i* ε i^2 ≤2)(hF:∀ᶠ i in l₀,Bf i-Bc i=Δfare G W)
include hb hn hα he0 hB hL hF
local notation "Θ!"=> fun i=> Adventure V X Y W (S i) (f i) (g i) (ε i)
set_option maxHeartbeats 200000
lemma ΡbFly :∀ᶠ i in l₀, Flyer ((Θ!) i) (W.val:ℝ) (Reven (κBit V) (Bc i) (Bf i)) :=by
        let Z(i:I):=(f i).ℳ; have ho: 0<Δfare G W:= hi_S (by omega) hs; exact Tavern _ (ψ) hT (Uclock X.cart f g Y.cart S hT hx hy hr) hz (ΦAct (Z!).Glp (Z!).Z a (vP).policy) (FruS V).2 (FruS V).1 ho hF he0 hB hL (hα.mono (fun t ht=> rayT X.cart (f t) Y.cart (g t) (S t) ht)) hb (αBit V hb hn)
end
end YM.OPE.Stroke

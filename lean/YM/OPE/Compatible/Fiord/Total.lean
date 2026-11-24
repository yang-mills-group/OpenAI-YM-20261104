import YM.OPE.Compatible.Fiord.Lace
import YM.OPE.Compatible.Tony.Femme
/-!
# From chamber-law estimates to the bound for the observed field difference

`νFee` and `unitsX` extract the chamber-law and field estimates from `IceD`.
As `β` tends to infinity, `χHear` applies `ζEarn` to prove the `VisionTag` bound
at exponent `q1` for the difference between `portrait` and the comparison field.
`Earτ` packages these estimates as `PassportIce` for a simple gauge group.
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
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
open GlowPack Silt.Phere Ibis Owl Lass Lass.Zest Spells Yolk Pill Dial Merchant Merchant.Sleeve
variable {L:PriceBook H T}{a:Axis}(V:Foyer L hs a l (l+6+6))(i:ℕ)(he:highStage L hs a V ≤ i)
variable (S:Stage)(X:BankW L hs a V he S.clip) (P:Pad G)
set_option quotPrecheck false
set_option maxHeartbeats 200000
local notation "F*"=> solar G (l+6+6) V.pay.st.τ
variable {n:ℕ→Side}{β:ℕ→ℝ} {ξ:ℝ}{r:ℕ}
variable (A:∀ j, HillZ (T:=T) S i r l ξ (β j) (n j))
variable (g:ℂ→L[ℝ]ℝ)
open Next.Scheduling CardinalQ
variable (ht:Tendsto β atTop atTop)(hp:∀ j,RichHill i S (A j))
open HillZ
variable (U:Scaffold atTop (Counters β) n (Mnd i S A) r)
local notation "F0"=> fun j=> portrait V i he S P (A j) g
variable (D:ℕ→ Law (Chamber G r))(x:ℕ→solar G (l+6+6) V.pay.st.τ)(p q:Forge G n)
variable (hx:IceD V i he S P A g U D x p q)
section
private lemma colored (R:Side)(x y:solar G k τ): inkM (Goan (x-y)) k (0:Site R)= inkM (Goan x) k (0:Site R)- inkM (Goan y) k (0:Site R):=by
        let Q(a:solar G k τ):= inkM (Goan a) k (0:Site R); have hh(a b):Q (a+b)=Q a+Q b:= by
            funext v; unfold Q Goan; erw[map_add]; exact Ink_sum _ _ _ _ k _ _ (resin a.val (m:=0) (fun _=>Nat.zero_le _)) (resin b.val (m:=0) (fun _=>Nat.zero_le _))
        change Q _ = _-_; apply eq_sub_of_add_eq; change Q _+Q y=Q _; rw [← hh,sub_add_cancel]
lemma tint_spec (j:ℕ): portrait V i he S P (A j) g=Ctag A g P (hazard V he) V.pay.st.hτ j:=rfl
include hx
lemma νFee: GaugeD A U D:=by
        refine ⟨fun j=>(hx.costs j).1,fun j y=>?_⟩; exact (hx.costs j).2 y
lemma unitsX: AcctΩ A U g P (hazard V he) (V.pay.st.hτ) (ego G n x) p q:=by
        let S0:=hx.seed; refine ⟨S0.manned.phased,hx.tender,fun i=>Eventually.of_forall fun j=>tBody _ _, S0.planet.pay,S0.fieldC.pay,?_⟩; apply hx.film.mono; intro j hj; rw[show Ctag A g P (hazard V he) (V.pay.st.hτ)=F0 from funext (fun i=>(tint_spec ..).symm)]; exact hj
include ht
lemma χHear : VisionTag V i he S P A g x:=by
       let hU:= unitsX V i he S P A g U D x p q hx; let v:=hazard V he
       let he' := νFee V i he S P A g U D x p q hx; have hT:=ζEarn A U D hs ht he' H g P v hU; obtain ⟨t,ht',hZ⟩:=hT.yod; unfold VisionTag; constructor; refine ⟨t,ht',?_⟩; filter_upwards [hZ,hx.film] with j hj hF; refine ⟨hj.1,?_ ⟩; let f:= portrait V i he S P (A j) g; let P:=ego G n x; change Spectre _ _ (Aview (f-x j) 0 _) _ _; let d0:= et A j; let vol_l:= l+6+6; have hp:Aview (f-x j) (0: Site (n j)) d0=Cameo.tariff d0 (q j-(P-p) j):=by
             change Cameo.tariff d0 (inkM (Goan (f-x j)) _ 0)=_; have heq:inkM (Goan f) (l+6+6) (0:Site (n j))- p j=q j:=hF; rw [colored, ← heq]; change _= Cameo.tariff d0 (_-_- (inkM (Goan (x j)) _ 0 - p j)); congr 1; abel
       rw[show Aview _ _ _= _ from hp]; exact hj.2
end
lemma SolvedIce (a : Axis) (h:G.Simple) : Visionτ h a:=⟨fun _ _ _ _ _ P j he S _ p _ _ _ _ ht _ A U q X B v u hx=> χHear P j he S p A q ht U B X v u hx⟩ 
lemma Earτ (a:Axis)(h:G.Simple) : PassportIce a h := Visionτ.Wish (SolvedIce a h)
end YM.OPE.Stroke

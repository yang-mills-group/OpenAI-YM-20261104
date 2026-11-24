import YM.OPE.Compatible.Lady.Curr
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
section
open Pressure ConnectedActivityE6 Shell Channel
variable {m:ℕ}{P:Teller G}{D:RG.Patch}{E:ConnectedActivityE6.Target G P}{Q:Side} {W C η:ℝ} {o:ConnectedActivityE6.Target.Order G W}
variable {L:I→Host K T}{p:∀ i,Wall D E Q o η C m (L i)}{V S A:I→ℝ}{l g:Filter I} {b e r' c C':ℝ}
variable (h: Chase (Eve p) l) {x:∀ i,Site (L i).c} {y z d:I→ℕ}(hn: Lite (Eve p) l (fun i=>‖(p i).w‖))
local notation "ζ"=> Eve p
local notation "ψ"=> Chase.σW (Eve p)
set_option quotPrecheck false
local notation "δA"=> fate (Eve p)
abbrev hPin (p:∀ i,Wall D E Q o η C m (L i))(d:I→ℕ)(n:ℕ)(i:I):= o_cover (L i).Z.patch (d i) (Chase.barM (Eve p) i) n
include h
lemma anyG (hn: Lite ζ l (fun i=>‖(p i).w‖)) :∃ j:ℕ,∀ᶠ i in l, ‖(Eve p i).g‖≤ Chase.billSp ζ j i:=by
        obtain ⟨j,hj⟩:= h.gain hn; refine ⟨j,?_⟩; filter_upwards [hj,h.Dscale] with i hi he; change ‖ψ i • (p i).w‖ ≤_; rw [norm_smul_of_nonneg he.1.le]; simpa only [norm_norm] using hi
variable (x:∀ i,Site (L i).c){n d':ℕ} (hd: Lite (Eve p) l (fun i=>(d i:ℝ)))
abbrev Hpools (x:∀ i,Site (L i).c)(d:I→ℕ)(i:I):= Ξ (L i) (rink (x i)) (d i)
noncomputable abbrev pond (x:∀ i,Site (L i).c)(p:∀ i,Wall D E Q o η C m (L i))(d:I→ℕ)(n:ℕ)(i:I): Homer (Eve p i) (x i) (d i) n (Hpools x d i):= fitted _ _ _ _ _ (Finset.Subset.refl _)
noncomputable abbrev fansU (x:∀ i,Site (L i).c)(p:∀ i,Wall D E Q o η C m (L i))(d:I→ℕ)(n:ℕ)(w:∀ i,AxisChart G (L i).ForestQ)(i:I):= burnS (x i) (d i) (hPin p d n i) (p i).w (w i)
omit h in lemma hip (n:ℕ)(i:I): d i ≤ hPin p d n i:=by unfold hPin o_cover circuitY rope; omega
omit h in lemma pond_A (d:I→ℕ)(n:ℕ)(i:I): (pond x p d n i).H= Ξ (L i) (rink (x i)) (hPin p d n i):= rfl
include hd
lemma hpools (n:ℕ): Lite ζ l (fun i=>(hPin p d n i:ℝ)):=by
       rw [show (fun i=>(hPin p d n i:ℝ))=(fun i=> (o_cover (Eve p i).V.patch (d i) (Chase.barM (Eve p) i) n:ℝ)) from rfl]; exact (h.trackSpan d hd (j:=n)).1
abbrev WinK (p:∀ i,Wall D E Q o η C m (L i))(n:ℕ)(i:I):=Chase.billSp (Eve p) n i
noncomputable abbrev Ψs (p:∀ i,Wall D E Q o η C m (L i))(n:ℕ)(i:I):=‖(p i).w‖ + 2*(WinK p n i/Chase.σW (Eve p) i)
include hn
omit hd in
lemma ΓΨ (n:ℕ):Lite ζ l (Ψs p n):= hn.add ((Lite.flatC (2:ℝ) h).rmul (h.PathJ n)) h
variable (hS:∀ᶠ i in l, (L i).Rich s c e (A i) u C' ∧ 0 ≤ A i) (hT:0<s)(he:0<e)(hc:0≤c)(ht: RateLE l (fate (Eve p)) A 0)
include hS hT he hc
-- before paying ext commit ceiling.s
omit hd hS hT he hc
lemma μmark (n:ℕ): Lite ζ l (fun i=>Pξ G s c u C' (Ψs p n i)):=by let f(t:ℝ):= Lite.flatC t h; have he:=ΓΨ h hn n; exact ((f _).rmul ((f _).rmul ((((f _).rmul ((f _).rmul he))).add he h))) -- uses no hS etc
include hS hT he hc
omit hn in lemma feet (v n t:ℕ)(hz:∀ q:ℝ,0≤ q→∀ᶠ i in l, crestPrice G (q*fate (Eve p) i)+Pξ G s c u C' (Ψs p v i)< WinK p t i/(2*Chase.σW (Eve p) i))(l':Filter I)(hr:l'≤ l)(X:∀ i,AxisChart G (L i).ForestQ)(hX:∀ᶠ i in l', Scale (fansU x p d n X i) (Ψs p v i))(ha:0<r):
       Bevel (fansU x p d n X) l' (fate ζ) ψ (WinK p t) r (-(1/2)):=by
           let H':= h.infΘ hr; let BW:= H'.LeapJ t; let Y:= fansU x p d n X; refine ⟨?_,by norm_num,H'.ζOpR.pays H'.tense,(H'.PathJ t).sound H',?_,(H'.Dscale).mono (fun i hi=>hi.2)⟩
           · filter_upwards [H'.ζOpR.pos,BW.2.2,((BW.2.1).tends (by norm_num) H'.tense).eventually (ge_mem_nhds ha)] with i hi hk he'; exact ⟨hi,hk,le_trans (div_le_self (show 0≤ WinK p t i from hk.le) (by norm_num)) he'⟩
           intro q hq; filter_upwards [(hz q hq).filter_mono hr,hS.filter_mono hr,hX] with i hi he' hp; exact lt_of_le_of_lt (add_le_add le_rfl (stareT he'.1 hT hc he hp)) hi
end
end YM.OPE.Lass

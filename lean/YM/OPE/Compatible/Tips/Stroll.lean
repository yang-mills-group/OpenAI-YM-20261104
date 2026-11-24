import YM.OPE.Compatible.Tips.Trip
import YM.OPE.Compatible.Rave.Orb
import YM.OPE.Compatible.Karls.Jay
import YM.OPE.Compatible.Hike.Piece
import YM.OPE.Compatible.Karls.Bent
import YM.OPE.Compatible.Karls.York
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Zc!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Cy"=> solar G d τ
open JetS
open Finset
open PriceZ Hark
open Hark Nestle StageLight Shrew Balsam
variable (hp:G.Simple)(hr:LocalRatio R)
include hr
lemma freezeZ (x y: solar G d τ)(S:Even c.val)(A:Alps K T i v)(C:Lit S A 0)(u v:Site c)(hi:4 ≤ i):
   let p:=cutφ S x.val u*cutφ S y.val v
   Homog (C.s.pay R p) (PriceZ.Warp A S hi hp u v x y R):=by intro p; exact Glass.capsule (bramble S) C (bredV A 0 S hi hp) hr p hi hp (prodMar (Pond S) (CloudH S x u) (CloudH S y v))
structure FairV {k:ℕ}(x:solar G d τ)(p: Saga G e k):Prop where
     era: twilight x.val
     cue :∀ n:Side,∀ y:Site n, Strike (d+(0:Phase).val) (worldR (τ 0) (d+(0:Phase).val) y _ (x.val 0))=Phi p firm (fence · y)
lemma pulseZ (T':Saga G e r)(S:Saga G e m)(x y:solar G d τ)(hx:FairV x T')(hy: FairV y S)(Q: Even c.val)(A:Alps K T i v)(u v:Site c)(he:4 ≤ i)(ht:A.gear=Train.top i)(h: StageLight.Track A c): (PriceZ.Warp A Q he hp u v x y R).s= (boost Q (Train.top i) he K.K (G:=G)).average (Chart.tangent G (Weir.Limb Q)) (Wish T' Q u*Wish S Q v):=by
   obtain ⟨p⟩:=Lit.buy Q A he hp 0; let Zc:=cutφ Q x.val u *cutφ Q y.val v; have hx':(Pond Q).Marbles Zc:= prodMar (Pond Q) (CloudH Q x u) (CloudH Q y v); have ha: (fun z=> (Zc z).s)= (Wish T' Q u * Wish S Q v):=funext fun i=> congrArg₂ (·*·) (alpha_eq T' hx.cue u i).symm (alpha_eq S hy.cue v i).symm
   rw [← show ((p.s.pay R Zc).s)=_ from (freezeZ hp hr x y Q A p u v he).1, ← ha]; exact (Shrew.payoff Zc p ht h hr hp (hx'.toll 0) (hx'.toll 1) (h:=he)).1
variable {U':Gloam}
lemma pastP (x y: solar G d τ)(V W:Nestle.Crew U')(H:∀ i, Even (U'.M i).val)(A:Alps K T i v)(p: Saga G e k)(q: Saga G e m)(ht:FairV x p)(hs:FairV y q)(hv:V ≠ W)(hw:SpareW V W)(hp':SpareW W V)(he:A.gear=Train.top i)(h:∀ i,StageLight.Track A (U'.M i))(hy:4 ≤ i) : Fruit U' (e+e) (fun i=> (PriceZ.Warp A (H i) hy hp (V.val i) (W.val i) x y R).l) 0:=by
      let a(j):= cutφ (H j) x.val (V.val j); let b(j):=cutφ (H j) y.val (W.val j); let X(j):=a j*b j; let P(j):= Classical.choice (Lit.buy (H j) A hy hp 0); have hh : (fun i=> (PriceZ.Warp A (H i) hy hp (V.val i) (W.val i) x y R).l)= (fun i=> (((P i).s.pay R (X i)).l)) :=funext fun i=>(freezeZ hp hr x y (H i) A (P i) _ _ hy).2.symm; rw [hh]
      refine (arc_apt H hy P X ?_ ?_ he h hr hp).2; swap
      · exact Tar.add (Tar_mul H (tip_tap H V x.val ht.era 0) (tip_tap H W y.val hs.era 1)) (Tar_mul H (tip_tap H V x.val ht.era 1) (tip_tap H W y.val hs.era 0))
      convert plume H p V W q hv hw hp' using 1; funext i v; exact congrArg₂ (· * ·) (alpha_eq p ht.cue _ v).symm (alpha_eq q hs.cue _ v).symm
end YM.OPE.Quit.Jac

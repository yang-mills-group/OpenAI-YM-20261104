import YM.OPE.Compatible.Kyoto.Sort
/-!
# Frame data at a prescribed order

A `Foyer` supplies phase cutoffs that dominate the stencil taxes at
orders `d`, `d + 1`, and `d + 2`. Under the order bounds of `Δtavern`,
one can prescribe its patch order. At every stage at least as large
as that order, `stepW` supplies the `BankW` coordinates for each clip.
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
section

open Balsam Nestle Pert.Full
structure Foyer (L:PriceBook H T)(hs:G.Simple)(a:Axis)(l d:ℕ) where
       pay:Sight L hs a l d
       heat : Aware (d+2) pay.st.τ
       vig (i:Phase)(e:ℕ)(he:e≤2): Variance.StencilTax (d+e) (l+l+1) ≤ pay.st.τ i
set_option maxHeartbeats 200000
variable (L:PriceBook H T)(hs:G.Simple)(a:Axis)
lemma Δtavern (p:ℕ)(hp:max 5 (l+3)≤p)(hd:l≤d): ∃ V:Foyer L hs a l d, V.pay.st.S.J=p:=by
        let k:= l+l+1; let X:=Finset.univ.sup (fun i: Fin 3=>Variance.StencilTax (d+i.val) k); obtain ⟨N,hN,hq,hv⟩:= behaviorX X L l d k p hp hd (hs:=hs); obtain ⟨W⟩:= contender (k:=l+l+1) N.Glp N.Z a (Nat.lt_succ_self _) N.hp N.holds N.receives N.tally N.sign; exact ⟨⟨⟨N,W⟩,hq,fun i j hj=> le_trans (show _≤X from (le_sup (f:=fun i: Fin 3=>Variance.StencilTax (d+i.val) k) (mem_univ (⟨j, by omega⟩:Fin 3)) )) (hv i)⟩,hN⟩ 
-- A cab fixes the stage and clip of its data and carries the lower bound on its fee.
structure Cab (T:Seasons K)(j:ℕ)(c:Clip) where
        fees:ℝ
        positive: 1 ≤ fees
        ℳ : Alps K T j fees
        clip : ℳ.clip=c
local notation "V0"=>Cab T j p
lemma Yelite :1 ≤ (fun x:Cab T j p=> x.fees):=fun i=> i.positive
abbrev highStage (V:Foyer L hs a l d) := V.pay.st.S.J
structure BankW (L:PriceBook H T)(hs:G.Simple)(a:Axis)(V:Foyer L hs a l d)(he:highStage L hs a V≤ j)(p:Clip) where
       Ω : Topic.Ω V.pay.st.Z (Cab T j p) Cab.fees
       cart : Cart V.pay.st.Glp V.pay.st.Z a V.pay.policy Ω Yelite (V.pay.st.S.order_cut.trans he) Cab.ℳ
       ear : Topic.Stone V.pay.st.Z Cab.fees Ω 
lemma stepW (V:Foyer L hs a l d)(he:highStage L hs a V≤ j)(p:Clip): Nonempty (BankW L hs a V he p):=by
       obtain ⟨Ω,h,h'⟩:= temperate a L V.pay he (Yelite (T:=T) (p:=p)) Cab.ℳ Cab.clip; exact ⟨Ω,h.some,h'⟩
end
end YM.OPE.Stroke

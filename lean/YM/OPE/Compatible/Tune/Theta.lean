import YM.OPE.Compatible.Tune.Stream
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Bounds for families of frame maps and existence at a prescribed level

`weatherQ` gives a uniform polynomial bound for `EFrame` when the maps on
tracts and the source and target price functions have such bounds in a
common parameter. For `l ≤ d` and `max 5 (l + 3) ≤ i`, `retina` chooses a
`Sight` at level `i`. At or above that level, `climate` constructs a `Cart`
for an `Alps` family with a common clip and `1 ≤ Y`.
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
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack


variable {vα:I→ℝ}{A:(x:I)→Alps K T j (vα x)}{V':Z.Ω I vα}{hp':4 ≤ j}{hz: 1≤vα}
variable (D':Cart Hp Z a W V' hz hp' A)(t:I)(U': Tracts G d τ →L[ℝ] Tracts G d τ)
local notation "G!"=> Gauge
local notation "T*!"=>LineCt W
variable {qβ:I→ℝ}{Vv:I→ Tracts G d τ→L[ℝ] Tracts G d τ}
lemma weatherQ {X:Q→ℝ}(f:Q→M)(g:Q→I)(N:Q→ Tracts G d τ→L[ℝ] Tracts G d τ)(h:Wealth N X 1)(hf:Wealth (Y∘ f) X 1)(hg:Wealth (vα∘g) X 1) : Wealth (fun q=> EFrame D (f q) D' (g q) (N q)) X 1:=by
       exact PledgeW (augW hg (fun i=> zero_le_one.trans (hz (g i))) (growth (q:=g) (pricedA' Hp Z a W V' hz hp' A D'))) (PledgeW h (augW hf (fun i=>zero_le_one.trans (hq (f i))) (growth (q:=f) (PelCost D))))
end
section
variable (N:PriceBook H T)(hd:l ≤ d)(hn:max 5 (l+3) ≤ i)
-- The frame cutoff in a `Sight` is `l + l + 1`.
structure Sight (L:PriceBook H T)(hs:G.Simple) (a:Axis)(l d:ℕ) where
       st : Coach H L hs l d (l+l+1)
       policy : GlowPack st.Glp st.Z a (k:=l+l+1)
include hn hd in
set_option maxHeartbeats 200000 in
lemma retina:∃ S:Sight N hs a l d, S.st.S.J=i:=by
       obtain ⟨v,hv⟩:= behaviors N l d (l+l+1) i hn hd (hs:=hs); obtain ⟨T⟩:= contender (k:=l+l+1) v.Glp v.Z a (Nat.lt_succ_self _) v.hp v.holds v.receives v.tally v.sign; exact ⟨⟨v,T⟩,hv⟩
set_option maxHeartbeats 200000 in
lemma climate (S:Sight N hs a l d)(he:S.st.S.J≤j)(hP:1≤ Y) (A:(x:M)→Alps K T j (Y x))(ht:∀ i,(A i).clip=p): ∃ U:S.st.Z.Ω M Y,Nonempty (Cart S.st.Glp S.st.Z a S.policy U hP (S.st.S.order_cut.trans he) A):=by
       obtain ⟨P,hP'⟩:= receiveLab S.st a (by omega) he A hP ht; exact ⟨P, envoy S.st.Glp S.st.Z a S.policy P hP _ A hP' S.st.tally S.st.sign ht⟩
end
end YM.OPE.Stroke

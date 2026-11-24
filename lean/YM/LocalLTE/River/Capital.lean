import YM.LocalLTE.Ballot.Lure
import YM.LocalLTE.River.Pulp
/-!
## Jobs, precision tariffs after ALL projections. For running normalized fields.

Operator budgets proportional, purchased in the construction with physical debts.
Uses the same post-mask weakening and actual schedule projection factors
as the body. This currency book prices regular contributions AFTER exposure of
the apt-mark ports. Not paying exceptional support with Ted/core denominator!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open ConnectedActivityE6
open Mallow Daisy Charity Lotus
variable {G:Gauge}
open YM.LocalLTE.Dilation Push.AbsoluteSums
variable (X:RG.Stage) (l d:ℕ) (L:Side) (e:ℝ)
local notation "K"=> Push.Local.factor (hol G) (localSection G d) X.supportExponent (Cub.title G X)
local notation "H"=> sill X.supportExponent l
set_option quotPrecheck false
local notation "z₀"=> ((L.val:ℝ)^d)
local notation "g"=> Doors.rate L
-- before derivative comparison at extended supports. positive on true.
variable (G)
noncomputable def regularNet (t:ℝ):ℝ:= 2*((L.val:ℝ)^d) *Turf.wadSong X.supportExponent (betaF G t L) e l
-- after projections, inherit curvature as well.Audit
noncomputable def debtR :ℝ:= K*(H*(g)) -- feeds existing regular error.
local notation "Tt"=> debtR G X l d L
-- forcing branch. Debit ratio *after* √w. given b=y=g*myst; Out:
-- E contribution.K y.K-after π. Util canopy from Patel. deliberately same bound for each not dual. hFit.K
noncomputable def debtK := (g)+ H*(g)+ K*(H*(g))
-- exceptional rate, pressure only
local notation "Nι"=> regularNet G X l d L e
variable {G}{S:Teller G} (Q:ConnectedActivityE6.Target G S)
noncomputable def flatX (μ t:ℝ):ℝ:= (Blush.glyph t)⁻¹*(2*((L.val:ℝ)^d)*(Q.goal L t)⁻¹ * straw μ L G t)
noncomputable def rareX (μ t:ℝ):ℝ:= flatX d L Q μ t+ lipK t*(H*(g))+lipK t*(K*(H*g))
-- provisional sums.Pays.Planet.K(C.Quarter).
-- Application row prices not guesswork. inherited principal.Caller.
noncomputable def seedY (t:ℝ) (trueCard pred err:ℝ):ℝ:= K*(H*((g)*trueCard)+(Nι t*pred+H*(g*err))) -- autoimplicit G in notation not inferred! add arg
noncomputable def seedE (μ t:ℝ) (trueCard pred err:ℝ):ℝ:= rareX X l d L Q μ t*trueCard+ K*(Nι t*pred+H*(g*err))
local notation "N'"=> Legato.Spool.regularNet
local notation "K'"=> Legato.Spool.debtK
section thresh
variable (G)
lemma sillS : 0 ≤ H:=Real.exp_nonneg _
lemma factorS:1 ≤ K:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (mul_nonneg (add_nonneg X.price_pos.le zero_le_two) (by positivity))) (Push.Local.atomPrice_ge_one _ _ (zero_le_one.trans (Cub.title_one ..)))
lemma debtR0 : 0≤ Tt:= mul_nonneg (zero_le_one.trans (factorS G X d)) (mul_nonneg (sillS X l) (Doors.rate_pos _).le)
lemma debtK0 : Tt ≤ K' G X l d L:= le_add_of_nonneg_left (add_nonneg (Doors.rate_pos _).le (mul_nonneg (sillS X l) (Doors.rate_pos _).le)) -- args order.
variable (t:ℝ)(hp:0< betaF G t L)
lemma flatQ {μ:ℝ}(Q:ConnectedActivityE6.Target G S) (hh:0< betaF G t L):0 ≤ flatX d L Q μ t:=by -- S implicit contains G. avoid binder
   unfold flatX; exact mul_nonneg (inv_nonneg.mpr (Blush.glyphpos t).le) (mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr (Real.rpow_nonneg hh.le _))) (mul_nonneg zero_le_two (Real.exp_pos _).le))
include hp
lemma rareQ {μ:ℝ} : 0≤ rareX X l d L Q μ t:=by -- include hp
   have ht:0≤ lipK t:= mul_nonneg (by positivity) (Blush.glyphpos t).le
   exact add_nonneg (add_nonneg (flatQ G d L t Q hp) (mul_nonneg ht (mul_nonneg (sillS X l) (Doors.rate_pos _).le))) (mul_nonneg ht (debtR0 G X l d L))
lemma regular0 : 0 ≤ Nι t:=by -- include
   unfold regularNet Turf.wadSong; exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (sillS X l) hp.le) (Real.rpow_nonneg hp.le _))
end thresh
local notation "Y"=> rareX X l d L Q
variable (μ:ℝ)
open Urns
lemma burst (hμ:0<μ)(a:ℝ): Rate G L a (Y μ):=by
       have he : Rate G L (-Q.rate) (fun x=>(Q.goal L x)⁻¹):=by
          refine Rate.congr Rate.power ((Delay.shift_pos G L).mono fun x hx=>?_); exact (Real.rpow_neg hx.le Q.rate).symm
       have hL := (he.mul (Blush.efferv (L:=L) (G:=G) hμ (Q.rate+a))).mul_left (2*z₀)
       have hg:Rate G L a (flatX d L Q μ):=by
           refine Rate.compare (Rate.weaken hL (by linarith only)) ?_
           apply Eventually.of_forall; intro x; apply le_of_eq; apply congr_arg abs; unfold flatX; ring
       have hx : Rate G L a lipK:=by
           have h:=Rate.radius_price (G:=G) (L:=L); have hh:Rate G L 0 (fun x=> ((Pressure.radiusB x + Pressure.radiusB x+1 :ℕ):ℝ)^4):=by simpa only [Nat.cast_add,Nat.cast_one,zero_mul] using! (((h.add h).add (Rate.const 1)).pow 4)
           simpa only [zero_add] using! (hh.mul (Mallow.cheapest (G:=G) L a)) -- cf Buttons
       exact (hg.add (hx.mul_right _)).add (hx.mul_right _)
variable (G)
lemma regain : Rate G L (1-e) (regularNet G X l d L e):=by
   have hu:Rate G L 1 (fun x=> H* betaF G x L):=(by simpa only [Real.rpow_one] using! ((Rate.power (G:=G) (L:=L) (a:=1)).mul_left (H)))
   let f x:= Turf.wadSong X.supportExponent (betaF G x L) e l
   have hh:Rate G L (1-e) f:=by simpa only [← sub_eq_add_neg] using! (hu.mul Rate.power)
   exact hh.mul_left _
end YM.PhysicalNext.Repeat.Legato.Spool

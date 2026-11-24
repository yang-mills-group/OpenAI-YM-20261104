import YM.LocalLTE.Ballot.Buttons
import YM.LocalLTE.Ballot.Yarn
/-! Repriced single-column clock. Standalone receipts eventually. Authenticator U.ac from *true* pillars. Additional universal staging.K reduction receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
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
open YM.LocalLTE.Dilation
namespace VoucherB
open Push.AbsoluteSums ConnectedActivityE6.Coat
-- Foreground exact parameters.Scale.
variable (X Y:RG.Stage){P:Teller G}(Q:ConnectedActivityE6.Target G P){L:Side}{a b ζ μ t x β E:ℝ}
variable {n:Side}(R:Rep G n) (M:Lotus.Leaf R)(l d r:ℕ)(c:Levels G)(m:ℕ)
local notation "Z"=> c.clock
local notation "P₀"=> c.params m
local notation "B" => c.budget m
local notation "K"=> c.clock.forcedAllowance m
local notation "f"=> Push.Local.factor (hol G) (localSection G d) X.supportExponent (title G X)
local notation "W"=> (((L.val:ℝ)^d))
local notation "v"=> (Real.sqrt (c.clock.forcedAllowance m))
local notation "σ" => (1:ℝ)
set_option quotPrecheck false
-- Proves bound without extra rate.So.Work current µ positive? no.%
lemma cull (he:VoucherB.Load Y X l r d L E Q μ t)(hβ: betaF G t L/2≤ β)(hx: β≤2*betaF G t L) (hp:c.clock.hatBeta m=t)(_hr:c.params m = X)(hτ:(R.p).mass M.crest M.weight ≤ ticR G Y) (_hz:0 ≤ a)(hw:a≤ Legato.cl0 Y d L) : let D:=jewelDebt M Q L t; let δ:= Real.sqrt K; let u:=Push.Local.hitWidth (c.budget m)* K /δ
     -- full leadP relative Bound root.Price
     let k:= Push.Local.factor (hol G) (localSection G d) X.supportExponent (title G X); let q:=k*(sill X.supportExponent l*a);
     δ⁻¹*(W*(D+D)*straw μ L G t)+u*(sill X.supportExponent l*a)+u*q ≤ ConnectedActivityE6.Coat.gStep β^((r:ℝ)+1):=by
    intro D δ u k q; have ht : 0<jewelDebt M Q L t+1:=by unfold jewelDebt; let α:= R.p.mass M.crest M.weight; have hp:0≤ R.p.mass M.crest M.weight:= M.profit.trans (R.p.loMass _ _ M.profit); have hx : 0 < Q.goal L t:=Real.rpow_pos_of_pos he.toll _; positivity
    have h : δ=Blush.glyph t:=by change Real.sqrt K=_; rw [Blush.glyph_eq,hp]
    have ha:0<δ:= h ▸ Blush.glyphpos t
    have hv: u= lipK t:=by
       unfold u lipK; rw [← h,show Push.Local.hitWidth B = (((Pressure.radiusB t+Pressure.radiusB t+1:ℕ):ℝ)^4) from (by unfold Push.Local.hitWidth; rw [Nat.cast_pow]; exact hp ▸ rfl)] -- edit order
       rw [← show δ^2=K from Real.sq_sqrt (by exact (forcedPos c m).le)]; field_simp
    have hF :1≤ k:= one_le_mul_of_one_le_of_one_le (Real.one_le_exp (mul_nonneg (add_nonneg X.price_pos.le zero_le_two) (by positivity))) (Push.Local.atomPrice_ge_one _ _ (zero_le_one.trans (Cub.title_one ..))) -- syntax
    have hM:0≤u:= div_nonneg (mul_nonneg (zero_le_one.trans (Push.Local.width_one_le _)) (Extra.Histories.forcedPos ..|>.le)) ha.le
    have h':D ≤ ticR G Y / Q.goal L t:=by
        let w:= R.p.mass M.crest M.weight
        exact div_le_div_of_nonneg_right ((mul_le_of_le_one_right (M.profit.trans (R.p.loMass _ _ M.profit)) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Q.usable.le) (by positivity)))).trans hτ) (Real.rpow_pos_of_pos he.toll _).le
    have hζ:0 ≤ LocalLTE.Dilation.sill X.supportExponent l:= Real.exp_nonneg _
    refine le_trans (add_le_add (add_le_add (b:=mintK (μ:=μ) Y d L Q t) ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hζ) hM)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hζ) (zero_le_one.trans hF)) hM)) ?_
    ·
      unfold mintK; rw [←h]; apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le); apply mul_le_mul_of_nonneg_right _ (show 0≤ straw μ L G t from mul_nonneg zero_le_two (Real.exp_pos _).le)
      rw [mul_right_comm 2 W,two_mul]; apply le_trans (mul_le_mul_of_nonneg_left (add_le_add h' h') (by positivity : 0≤W)); apply le_of_eq; ring
    rw [hv]; exact (he.money β hβ hx).2
end VoucherB
end YM.PhysicalNext.Repeat.Legato

import YM.LocalLTE.River.Capital
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
variable {S:Teller G} (Q: ConnectedActivityE6.Target G S)
local notation "Nι"=> regularNet G X l d L e
variable (C:Levels G)(m f:ℕ){μ t x a b:ℝ}(ht:C.clock.hatBeta m=t)(hβ:0< betaF G t L)
variable {n:Side}
local notation "v"=> Push.Local.hitWidth
lemma stampL (ht:C.clock.hatBeta m=t):v (C.budget m)*C.clock.forcedAllowance m/(Real.sqrt (C.clock.forcedAllowance m))= lipK t:=by
    let d:=Real.sqrt (C.clock.forcedAllowance m); have h:d=Blush.glyph t:=by unfold d; rw [Blush.glyph_eq,ht]
    unfold lipK; rw [← h,show Push.Local.hitWidth (C.budget m) = (((Pressure.radiusB t+Pressure.radiusB t+1:ℕ):ℝ)^4) from (by unfold Push.Local.hitWidth; rw [Nat.cast_pow]; exact ht ▸ rfl)]
    have hp:0< d:= Real.sqrt_pos.mpr (forcedPos ..); change _ * _ / d=_; rw [← show d^2=C.clock.forcedAllowance m from Real.sq_sqrt (by exact (forcedPos C m).le)]; field_simp
include hβ ht
-- conditions payment chart.T can fund.
lemma grainQ {c:Side}(R:Rep G c) (M:Lotus.Leaf R)(hp:R.p.mass M.crest M.weight=a) : let u:= g*a
    let V:=jewelDebt M Q L t; let δ:=Real.sqrt (C.clock.forcedAllowance m)
    let b:=Push.Local.hitWidth (C.budget m)* C.clock.forcedAllowance m/δ
    (δ)⁻¹*(z₀*(V+V)*straw μ L G t)+b*(H*u)+b*(K*(H*u)) ≤ rareX X l d L Q μ t*a :=by
      intro u V δ b; have h :δ=Blush.glyph t:= by change Real.sqrt _=_; rw [Blush.glyph_eq,ht]
      have he:b= lipK t:=stampL C m ht
      unfold rareX; rw [← he]; calc
        _ ≤ (flatX d L Q μ t*a)+b*(H*u)+b*(K*(H*u)) :=by
           apply add_le_add (add_le_add _ le_rfl) le_rfl
           unfold flatX; rw [h]; let k:= Blush.glyph t
           let q:= Q.goal L t; have hV: 0< q:= Real.rpow_pos_of_pos hβ _
           have hx: V≤a *q⁻¹:=by
               unfold V jewelDebt; rw [hp]; have hp:0≤a:= (M.profit.trans (R.p.loMass _ _ M.profit)).trans_eq hp
               rw [div_eq_mul_inv]; refine mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hp ?_) (inv_nonneg.mpr hV.le)
               exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Q.usable.le) (by positivity))
           exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hx hx) (by positivity : 0≤z₀)) (show 0≤ straw μ L G t from mul_nonneg zero_le_two (Real.exp_pos _).le)) (inv_nonneg.mpr (Blush.glyphpos t).le)) (le_of_eq (by unfold q; ring))
        _ = _:=by unfold u; ring
end YM.PhysicalNext.Repeat.Legato.Spool

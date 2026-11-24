import YM.MSbar.Wave.Reading
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Spin
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open Gauge Lattice Wilson RG Tree Precision Exterior Push Push.Uniform
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
open Set MvPolynomial Analysis
local notation "µ"=> PowerSeries.coeff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "X"=> Positions (Primary n G)
local notation "V"=> Directions G n
local notation "ϑ"=> fieldDir G n 1
variable (R:PathData G)(p:Clip)(F:Nesting G n)(q:ℕ) {S:ℝ → Config G n→ℝ}
def panel (G:Gauge) (n:Side) : Positions (Primary n G) ≃L[ℝ] Directions G n := (tint G (Body 1 n)).trans <| LinearEquiv.toContinuousLinearEquiv ({
    toFun:= fun i=> collect G i
    invFun:=fun x b=> x (b.1,axisEquiv.symm b.2)
    left_inv:=fun i=>funext (fun b=>by obtain ⟨x,i⟩:=b; obtain ⟨z,rfl⟩:= axisEquiv.surjective i; simp [collect,show axisEquiv.symm (coord z)=z from axisEquiv.symm_apply_apply z])
    right_inv:=fun i=>funext (fun b=>by obtain ⟨x,i⟩:=b;simp [collect,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i])
    map_add':=fun x y=>rfl
    map_smul':=fun x y=>rfl } : fieldDir G n 1≃ₗ[ℝ]Directions G n)
lemma draws (t:ℝ)(v:V): postcard G n t ((panel G n).symm v)= increment 1 (t•v):=by
   let L:=panel G n; change increment 1 (L (t•L.symm v))=_; rw [map_smul,L.apply_symm_apply]
local notation "T"=>tariff n q p R F
variable (h:Trend S F R p q)
noncomputable def joy(F:Nesting G n)(i:ℕ)(x:Positions (Primary n G)):=eval x (PowerSeries.coeff i F)
include h
lemma invariant (x y:Positions (Primary n G))(he:∀ᶠ t in Γ,S t (postcard G n t x)= S t (postcard G n t y)) (i:ℕ)(hh:i≤q) : joy (tariff n q p R F) i x=joy (tariff n q p R F) i y:=by
    apply sub_eq_zero.mp; let D(j:ℕ):= joy T j x-joy T j y
    have hv:=equivalence q p R F h (Price.fromConst x) (Price.fromConst y) he; refine magnitude (n:=q) (f:=D) ?_ i hh
    refine Price.egress hv (Eventually.of_forall (fun t v _=>?_)); unfold taste; dsimp only; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; unfold picture D joy; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,mul_sub]
-- Edge-colored constants. Port across.Rank.Period.O
open AnalyticBridge.VerifiedReset
variable (i:ℕ)(hi:i ≤ q)
include hi
abbrev weather (f:Nesting G n)(i:ℕ): Directions G n→ℝ:= joy f i ∘ (panel G n).symm
lemma allC(k:G.El)(x:Directions G n) : weather T i (colorMove k x)=weather T i x:=by
    apply invariant R p F q h _ _ _ i hi; filter_upwards [h.base] with x h'; rw [draws,draws, ← map_smul, exp_move, h'.1.shield]
lemma allS (k:Signed)(b:Site n)(x:Directions G n): weather T i (pullDir k b x)=weather T i x:=by
    apply invariant R p F q h _ _ _ i hi; filter_upwards [h.base] with t h'; rw [draws,draws, ← map_smul,pull_increment]; exact h'.1.even_ ..
noncomputable def bandE (k:Signed)(b:Site n): Positions (Primary n G)→L[ℝ]Positions (Primary n G):= ((panel G n).symm.toContinuousLinearMap).comp <| (pullDir k b).comp ((panel G n).toContinuousLinearMap)
noncomputable def hue (k:G.El): Positions (Primary n G)→L[ℝ]Positions (Primary n G):= ((panel G n).symm.toContinuousLinearMap).comp <| (colorMove k).comp ((panel G n).toContinuousLinearMap)
lemma inh (k:G.El)(x:X): joy T i (hue k x)=joy T i x :=by nth_rw 2 [← (panel G n).symm_apply_apply x]; exact allC R p F q h i hi k ((panel G n) x) -- nth rw maybe both
lemma ins (k:Signed)(b:Site n)(x:X): joy T i (bandE k b x)=joy T i x := by nth_rw 2 [← (panel G n).symm_apply_apply x]; exact allS R p F q h i hi k b ((panel G n) x)
-- Constant vector Ward consequences. Build for any f ContDiffAt on germs.
end YM.MSbar.Wave

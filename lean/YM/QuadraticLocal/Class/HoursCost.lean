import YM.QuadraticLocal.Class.Hours
import YM.QuadraticLocal.Qarry
/-!
# Credit facts on the close continuation. Costs on ALL positions permitted
 at these indices, same roof, age verified.Depending close length with chosen
 relative error factor. Here ε parameter in practical x^(ε) notation
 (βhat clock cost convention, not g; convert in Reports with all leases).

 `Ψ` unmarked sources used in Budget.hint.G., not quantified at this stage
 because it holds along ANY till Lens representation. No fixed-period witnesses in
 cost_k. CAN reuse Calendar stationarity proof.Be.Scope. Uses true Authority PaceCost.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent.Sycamore
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open PaceR
open AllOrder.Catch Mentor
variable {G : Gauge} (R:Run G)(g:G.Simple)
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "A" => R.alloy.B.a
variable {m i b k N:ℕ} {Q ε δ p q x y:ℝ} (hp : 0 < ε)(hP : ε ≤1/8)
variable (U:Syl.School k) (hQ : 0≤Q) (l N:ℕ)
local notation "Y"=> (Φ b)
local notation "M"=> U.order
local notation "E"=> (Sycamore.notice R b U ε)
local notation "τ"=> ( Sycamore.tol U ε )
local notation "τ'"=> ( Sycamore.tol U (ε/2) )

noncomputable def daily (i:ℕ) := ( R.alloy.B.a.clock.hatBeta (i+1))^( Mentor.Tuition.need U.order ( Mentor.Tolerance ( R.alloy.B.a.clock.J i )))
local notation "r"=> (roof R m b)
include g
lemma too : Tendsto Φ atTop atTop:= (tendsto_const_nhds.add_atTop ( (A).S.divergent.const_mul_atTop (Gauge.slopeConstant_pos g))) -- hp unnecessary ensure omit
omit g
lemma needed (hP:ε≤1/8): Sycamore.tol U ε≤ -(1/4:ℝ):= by unfold tol graded; push_cast; linarith only [hP,Nat.cast_nonneg (α:=ℝ) U.order]
lemma lives_pos : 0 < daily R U i:=Real.rpow_pos_of_pos (positive R (i+1)) _
lemma younger : Burn.young (Φ (i+1)) k ≤ Sycamore.daily R U i:=by
    unfold daily Burn.young; apply Real.rpow_le_rpow_of_exponent_le ((A).fits.delayed (i+1)).le; rw [Burn.sale_eq k]; unfold Tuition.need Catch.graded; have he:0<Tolerance ((A).clock.J i):=by unfold Tolerance; positivity
    have h:U.order≤ Burn.horizon k+1:=U.price
    push_cast; have h : (U.order:ℝ)≤ Burn.horizon k+1:= (by exact_mod_cast h); unfold Burn.horizon at h; push_cast at h; linarith -- parse
-- κ.Space.Y.Health.Widget.Calendar. Norm sup over indices and all fixtures.
include g hp hP
lemma ages : ∀ᶠ b in atTop,∀ m≤ b, Close R l Q m b → ∀ i:ℕ,m ≤ i → i < b → Sycamore.daily R U i ≤ Sycamore.notice R b U ε:=by
    obtain ⟨n,hn⟩:= exists_nat_gt (ε/2)⁻¹; let hh := Sycamore.too R g; let T:ℝ:= Sycamore.tol U (ε/2); let F:=(2:ℝ)^(-T); have ht:T≤-(1/4:ℝ):= Sycamore.needed U (by linarith only[hP]); let hW:= tendsto_rpow_atTop (half_pos hp); filter_upwards [ covers_hat R g l Q, on_tail R g l Q n, (hW.comp hh).eventually_ge_atTop F ] with b h hx ht₁ m hm hC i hi hb
    let G₀ := Φ b; have hp₁:0<G₀:= positive R b; have ht₂:1<Φ (i+1):= (A).fits.delayed _; let j:= (A).clock.J i
    have hp0 : n≤j:= (hx m hm hC).trans ((A).fits.mono hi); have hv: Mentor.Tolerance j≤ε/2:= by
       unfold Tolerance; rw [ one_div ]; exact ((inv_anti₀ (inv_pos.mpr (half_pos hp)) (hn.le.trans (Nat.cast_le.mpr (Nat.le_trans hp0 j.le_succ)))).trans_eq (inv_inv _)) -- cast glue
    calc
       _ ≤ (Φ (i+1))^ T:= Real.rpow_le_rpow_of_exponent_le ht₂.le (add_le_add_right hv _)
       _ ≤ (G₀/2)^T := Real.rpow_le_rpow_of_nonpos (half_pos hp₁) (h _ m (Nat.le_succ_of_le hi) hb hC) (ht.trans (by norm_num))
       _ = G₀^T * F:=by rw [ Real.div_rpow hp₁.le zero_le_two, div_eq_mul_inv, (show F=( (2:ℝ)^T )⁻¹ from Real.rpow_neg zero_le_two _ ) ];
       _ ≤ (G₀)^T * G₀^(ε/2):= mul_le_mul_of_nonneg_left (show F≤G₀^(ε/2) from ht₁) (Real.rpow_pos_of_pos hp₁ _).le
       _ = Sycamore.notice R b U ε:= (Real.rpow_add hp₁ T (ε/2)).symm.trans (congr_arg (fun p:ℝ=>G₀^p) (by unfold T tol; linarith)) -- unfold order okay?
-- Education evaluation.In.per

structure Attends (U:Syl.School k)(ε:ℝ)(m b d:ℕ):Prop where
    clocksK (i:ℕ) : m≤ i → Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i ∧ (d+4) ≤ R.alloy.B.a.clock.J i
    youth i (h:m ≤ i) (he:i<b): Sycamore.daily R U i ≤ notice R b U ε
    seat (i:ℕ) (hp:m ≤ i)(h:i≤ b): life R i b U ε ≤ 1
    hope : (roof R m b)^(2*U.pieces)*(life R m b U ε) ≤ notice R b U (2*ε)
    affair : (roof R m b)^(8*U.pieces) ≤ R.alloy.B.a.clock.hatBeta b
    finance : (roof R m b)^(2*U.pieces+2) ≤ (R.alloy.B.a.clock.hatBeta b)^ ε
    half i (h:m ≤ i)(he:i≤b) : R.alloy.B.a.clock.hatBeta b/2 ≤ R.alloy.B.a.clock.hatBeta i
    track : 2^(d+4)≤ R.alloy.B.a.clock.hatBeta b
local notation "xΦ" i:max=> Sycamore.life R i b U ε
include hQ
lemma learners (d:ℕ) : ∀ᶠ b:ℕ in atTop,∀ m≤b, Close R l Q m b → Attends R U ε m b d:=by
    filter_upwards [ (Sycamore.too R g).eventually_ge_atTop (2^(d+4)), on_tail R g l Q (Burn.horizon k+2), on_tail R g l Q (d+4), gives R g l (U.pieces*2+Sycamore.bill U) Q hQ ε hp, gives R g l (8*U.pieces) Q hQ 1 zero_lt_one, gives R g l (2*U.pieces+2) Q hQ ε hp, gives R g l (Sycamore.bill U) Q hQ ε hp,covers_hat R g l Q, Sycamore.ages (Q:=Q) R g hp hP U l] with b hD hN hE hJ hι hK h hp₁ hM m hm hv;
    let p:=Sycamore.tol U ε; let f:= Φ b; have he:1<f:=(A).fits.delayed _; have ht:0<f:= positive R b
    let a:=roof R m b; refine ⟨fun i hi=>⟨le_trans (hN m hm hv) ((A).fits.mono hi),le_trans (hE m hm hv) ((A).fits.mono hi)⟩, hM m hm hv,fun i hi hu=> ?_, ?_, (hι m m le_rfl hm hv).trans_eq (Real.rpow_one (Φ b)), hK m m le_rfl hm hv, fun i hi hk=>hp₁ i m hi hk hv, hD ⟩; -- Real.rpow_one ambiguous ▸
    · apply le_trans (b:= f^(ε+p)) _ (Real.rpow_le_one_of_one_le_of_nonpos he.le (by change ε+ Sycamore.tol U ε≤0; linarith only [Sycamore.needed U hP, hP])); rw [Real.rpow_add ht]; exact mul_le_mul_of_nonneg_right ( h m i hi hu hv ) (Real.rpow_nonneg ht.le _)
    unfold notice life; rw [ ←mul_assoc, ← pow_add, show tol U (2*ε)=ε+p from (by unfold p tol; ring),Real.rpow_add ht]; exact mul_le_mul_of_nonneg_right (by rw [ Nat.mul_comm 2 ]; exact hJ m m le_rfl hm hv) (Real.rpow_pos_of_pos ht _).le
end YM.QuadraticLocal.Advent.Sycamore

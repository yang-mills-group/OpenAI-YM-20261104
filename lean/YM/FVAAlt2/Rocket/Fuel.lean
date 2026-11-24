import YM.FVAAlt2.Rocket.Matrices
import YM.RegulatorIR.Centered.Breadth
/-!
# Admissible diagonal order estimates. More general than uniform family from manuscript
all assertions need this simultaneous thermal *count* schedule prior to using.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Rocket
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Topology Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain RegulatorIR.Profiles Sources Labels Source Momentum
open Oracle Atlas Epoch Calibration Kick YM.FVAAlt2
open MS MS.Menus MS.Dial MS.Land MS.Vista MS.Fleet MS.Tide MS.Orbit MS.High MS.Port
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}{u b p r:ℕ}{M:X→ℕ}{n:Page M→Side}{G:Gauge}
variable (S:Oracle.Circuit M n){K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P: Patch,P.Branches K G) {B:Epoch.Marked M}
variable {g:G.ColorIndex}{γ c₀:ℝ}(F: Calibration.Tent M){x:X→Room}{L:Meter X}
local notation "AΘ"=> S.payroll Y G Z (sheet F)
local notation "Σ'"=> S.dialect Y G Z (sheet F)
local notation "η"=> native M
local notation:max "P_" w:max => Page.opening M w
variable (J:Choice M)
variable (θ:X→ℝ) (ε:X→ℝ)(l:Filter X)
open Real
set_option quotPrecheck false
local notation:max "Ω" i:max=> (Σ').modifyErr 0 1 γ J i
structure Pace (L:Meter X): Prop where
   account : Poly L (fun i=> ‖exp (θ i)‖ₑ)
   spread r (hp:0≤r) : ∀ᶠ i in l,r*(θ i+ log ( L.val i ).toReal)≤ log (S.l (J.choose i))
local notation:max "kZ" i:max=> S.l ( J.choose i )
lemma aboveR (L:Meter X)(t:X): 1≤ (L.val t).toReal:= ENNReal.toReal_one ▸ ENNReal.toReal_mono (L.below _) (L.above _)
lemma headroom (i:Page M): S.l i≤ S.P i.bindW:= by rw [ ← S.comet i ]; apply le_mul_of_one_le_right (S.l_p _|>.le); exact_mod_cast (n i).property
variable {J θ l}
local notation "WZ"=> wage S Y Z F J γ
lemma debit_warm(i:X)(h₁:0<γ)(h₂:γ<1)(h:S.l (Page.opening M i)=1): Ω i ≤ 3 * (Real.exp ((γ/2)* log (kZ i) ))⁻¹:=by
    let z:= kZ i; let P:= S.P i
    have hp: z≤P:= headroom S (J.choose i)
    have hx:1≤z:= h ▸ show S.l _≤S.l (J.choose i) from ((Σ').heads (J.choose i))
    have hP:0<P:= zero_lt_one.trans_le (hx.trans hp)
    have hk:0<z:= zero_lt_one.trans_le hx
    unfold modifyErr transferErr IR₁ IR₀; rw [pow_zero,inv_one,one_mul,pow_one]; change P⁻¹ +(P^(γ/2))⁻¹+ (z^γ)⁻¹≤3*( exp ((γ/2)*log z) )⁻¹
    rw [mul_comm (γ/2:ℝ) (log z), ← Real.rpow_def_of_pos hk]; set q:= γ/2
    have hv: z^q≤P^q:=Real.rpow_le_rpow hk.le hp (by unfold q; positivity)
    have hl: z^q ≤ z^γ:= Real.rpow_le_rpow_of_exponent_le hx (by unfold q; linarith)
    have hr : z^q ≤ P:= hv.trans (Real.rpow_le_self_of_one_le (hx.trans hp) (by unfold q; linarith))
    have h:0<z^q:=by positivity
    linarith only [inv_anti₀ h hv, inv_anti₀ h hl, inv_anti₀ h hr]
lemma paints (H:Pace S J θ l L)(h:∀ i, 0 ≤ θ i)(k:ℕ)(v:ℝ)(hv:0<v)(a:ℝ)(ha:0<a): ∀ᶠ i in l,(L.val i).toReal^k * ( Real.exp (a*log (kZ i)) )⁻¹ ≤ exp (-v* θ i) :=by
    let R:ℝ:=(( k:ℝ )+v)/a
    filter_upwards [H.spread R (by unfold R; positivity)] with i hi
    let f:= (L.val i).toReal; let z:= kZ i
    have hz:z>0:=S.l_p _; have hf:0<f:=zero_lt_one.trans_le (aboveR L i); have h':0≤ log f:= Real.log_nonneg (aboveR L i)
    rw [←Real.exp_neg,←exp_log (show 0<(L.val i).toReal from hf)] -- rewriting in hi? avoid
    rw [ ← Real.exp_nat_mul,← Real.exp_add, Real.exp_le_exp ]; unfold R at hi; change ((k:ℝ)+v)/a*(θ i+ log (L.val i).toReal)≤ log ( S.l (J.choose i) ) at hi; rw [div_mul_eq_mul_div, div_le_iff₀ ha] at hi; nlinarith only [hi, mul_nonneg hv.le h',mul_nonneg (h i) (Nat.cast_nonneg (α:=ℝ) k)] -- k handling implicit
section join
variable {T:Trial X I}{D:X→ℂ}
lemma paceρ (H:Pace S J T.profile.θ l L) (h:0<γ)(hk:γ<1)(K:Carry L WZ fun i=> ‖D i‖ₑ)(hP:∀ w,S.l (P_ w)=1)(v:ℝ)(hv:0<v): PeakT l T.profile v D:=by
     have hX(w:X):0≤Ω w:= add_nonneg ((Σ').transfer_pos _|>.le) (inv_nonneg.mpr (Real.rpow_nonneg ( (Σ').hl _ |>.le ) _))
     obtain ⟨A,t,hA,H'⟩:=Centered.Carry_rt hX (g:=fun i=> ‖D i‖) (by simp; exact K)
     refine ⟨max 1 (3*A),lt_max_of_lt_left zero_lt_one, ?_⟩; filter_upwards [paints S H T.profile.room t v hv (γ/2) (by positivity)] with i hi; specialize H' i; rw [Real.norm_of_nonneg (norm_nonneg _)] at H'; obtain he:= debit_warm S Y Z F (J:=J) i h hk (hP i)
     calc
       _ ≤ _:= H'
       _ ≤ (3*A) * ((L.val i).toReal^t*( exp ((γ/2)* log (kZ i)) )⁻¹):= (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)
       _ ≤ _:= mul_le_mul (le_max_right ..) hi (by positivity) (by positivity)
end join
end YM.RegulatorIR.FVAAlt2.Rocket

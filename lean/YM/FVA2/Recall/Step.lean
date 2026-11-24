import YM.FVA2.Recall.Price
/-!
 # Commit a new common-perturbation-clock Ray. Covariance of the actual RG10 algorithm

 This does not replace the Gear from the shared prescription. Allows passage to and computation
 in another clock orientation (log links rescaled with another common unit, e.g. $g_i$) of
 all these symbols. Keep every source mark, transport their Laurent powers separately.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall.Move
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint Euler PertExtension PertExtension.Series Radial GaussianScore Facade Lattice RG
open Tested OpenSlots.Quadratic Precision Chart BlockGauge MultiGauge.Blocking Fabric Papers Line Roof Router
open scoped Classical Topology BigOperators ContDiff
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable (m:Move)
variable (a:Quadratic E)(k:ℕ)
local notation "A"=> Move.adjust m a.P
-- k extra eliminated parameters before now. μ factors consistent

def extra : Ticket E:= carry (E:=E) (m.p^k)
def twist : Ticket E := extra (E:=E) m k * Move.adjust m a.P
abbrev inclineX (p:Ticket E) := twist m a k * m.walk E p
lemma hype : incline (twist m a k):= pool (show incline (Move.extra (E:=E) m k) from (by unfold incline Move.extra; rw [←coeff_zero_eq_constantCoeff_apply,carry,coeff_map,coeff_zero_eq_constantCoeff_apply,map_pow,show constantCoeff m.p=1 from m.starts,one_pow,map_one])) (Stack.initial ..)
lemma pocket (A':Ticket E)(h:incline A'): incline (inclineX m a k A'):= pool (m.hype a k) (( m.constantLead A' ).trans h)
lemma dragT (d:F→ₗ[ℝ] E) : boost d (twist m a k) = twist m (drag d a) k := by rw [Move.twist,map_mul,Move.extra,unsigned,folds m d («A»:=a.P) (B:=(drag d a).P) (fun _=>rfl) ]; rfl -- A shadow macro

section contracts
open Quadratic
variable (q:Quadratic (E×F))[MeasurableSpace E][BorelSpace E] (μ: Measure E) [μ.IsAddHaarMeasure] (p:(core q).RespectsPrice) (x:Ticket (E × F))
lemma absorb : uptake q μ p (inclineX m q k x)= inclineX m (reduced q p) (k+Module.finrank ℝ E) (uptake q μ p x) := by
 unfold inclineX twist extra; rw [mul_assoc ( carry _ ), show uptake q μ p (carry _ * (_* _))=carry (m.p^k) * uptake q μ p (Move.adjust m q.P * m.walk (E×F) x) from ( tender _ (m.p^k) (Move.adjust m q.P * m.walk (E×F) x) ), receipt_u, pow_add,map_mul ]; ring -- tender
-- observable, distinct. normalized denominator uses exactly this income.
lemma label (W:Ticket (E × F))(hx:incline W) : Quadratic.fit q μ p (m.walk (E × F) x) (inclineX m q k W)= m.walk F (Quadratic.fit q μ p x W):= by
 apply (worth (Quadratic.upright q μ p ( m.pocket q k W hx ))).mul_left_cancel
 rw [fit_eq _ _ _ _ _ (m.pocket q k W hx), show inclineX m q k W * _= inclineX m q k (W*x) from (by unfold inclineX; rw [mul_assoc,map_mul]), absorb,absorb]; unfold inclineX; rw [mul_assoc (twist _ _ _), ← map_mul (m.walk F), fit_eq q μ p _ _ hx]
end contracts

variable {G:Gauge}{c f n:Side}{S:StepData c f} (H:S.patch.Branches S.kernel G)(t:S.Choices)(P:Inside S.ratio) {J: ChartRatio G} (hj:LocalRatio J)
structure Frames (k:ℕ)(U V:Unmasked G n) : Prop where
 top : U.Q=V.Q
 wage : inclineX m U.Q k U.W=V.W

namespace Frames
variable (k:ℕ) {U V:Unmasked G f} (u:Frames m k U V)
variable (w:PowerSeries ℝ)(W: Ticket (Flats G f))
local notation "E₀"=>Cross (G:=G) S P
local notation "Ω"=> m.walk ( Cross (G:=G) S P × Flats G c )
local notation "Φ"=> m.walk ( Flats G c )
local notation "r"=> Move.weight m w
local notation "Z"=> gated P U t w
local notation "Γ"=> gated P V t r
local notation "μ"=> tangent G ( Blocking.Index S P )
set_option quotPrecheck false
include u
lemma Gate : Z=Γ:= by unfold gated; rw [ ← u.top ]; exact congr_arg ( addOn (drag _ _) ) ( Hearth.quads ( m.tenure w ( substep (G:=G) P t ) ))
include H
lemma receives (J:ChartRatio G) : inclineX m Z k (receipt P t J w U)= receipt P t J (m.weight w) V:= by
 unfold inclineX twist extra receipt; rw [m.renew _ _ ( subStill P t H ), ← u.wage ]; unfold inclineX; rw [map_mul (boost (blankRight P)), m.dragT ]; unfold Move.twist Move.extra
 let K:= LinearMap.fst ℝ (Cross (G:=G) S P) (Flats G c); rw [_root_.map_mul Ω,_root_.map_mul Ω, boots, boots, show m.walk (Cross (G:=G) S P) _=_ from (m.light J ( Blocking.Index S P ))] -- order boots
 rw [m.combined _ (drag (blankRight P) U.Q).P (genesis w (substep (G:=G) P t)).P (fun _=> rfl)]; ring
variable (b:(core (gated P U t w)).RespectsPrice) (b':(core (gated P V t (Move.weight m w)) ).RespectsPrice)
-- do not imply patch mean scaling without determinant.
lemma tomorrow : Frames m (k+Module.finrank ℝ (Cross (G:=G) S P)) (Update P t J w U b) (Update P t J (m.weight w) V b'):= by
 have he:= Gate m t P k u w
 obtain ht:= absorb m k Z μ b (receipt P t J w U); have hv:= receives m H t P k u w J; rw [hv] at ht
 unfold Update; refine ⟨ ?_, ht.symm.trans ?_⟩; · change reduced Z b=reduced Γ b'; congr 1
 change uptake Z μ b _= uptake Γ μ b' _; rw [show uptake Z μ b = uptake Γ μ b' from (?_ : _)]; congr 1
lemma projects (A':Ticket (Cross (G:=G) S P × Flats G c))(hx: incline U.W) (hj:LocalRatio J): m.walk (Flats G c) (Broadcast P t J w U b A') = Broadcast P t J (m.weight w) V b' (m.walk (Cross (G:=G) S P × Flats G c) A'):= by
 have ht:= label m k Z μ b A' ( receipt P t J w U ) ( OpenSlots.along hj w hx ); unfold Broadcast
 rw [receives m H t P k u w J] at ht; rw [← ht, show fit Z μ b=fit Γ μ b' from (?_ : _) ]; congr 1; exact Gate m t P k u w
end Frames
end YM.FVA2.Recall.Move

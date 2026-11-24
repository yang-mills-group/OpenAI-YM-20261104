import YM.RegulatorIR.Venture.Hues

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Venture
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
open Epoch VacDay
/-! Gain plus slack and damping on χ. Does not bind projections. -/
open Epoch.League
variable {X I:Type} {M:X→ℕ}{n:Page M→Side} {K:KernelChoices}(S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(s:Page M→Scale){B:Marked M}
variable {p e u r:ℕ} {γ θ:ℝ} {Q : Page M→ℝ≥0∞}
section V
variable {X':Type}{M':X'→ℕ}{n':Page M'→Side} (S':Circuit M' n')(s':Page M'→Scale)(A:Section S S'){B':Marked M'}
local notation "χ"=> chi S Y G Z s
local notation "χ'"=> chi S' Y G Z s'
local notation "Ω₁"=> lnk S G
local notation "Ω₂"=> lnk S' G
local notation "A₀"=> S.devices Y G Z s
local notation "A₁"=> S'.devices Y G Z s'
local notation "β"=> B.age_t
local notation "α"=> B.age_f
section duel
-- inherit pose.B calibrations no clocks escape.
local notation "U₀"=>S.payroll Y G Z s
local notation "U₁"=> S'.payroll Y G Z s'


def focusD (e r:ℕ) (i:Page M):Packet (Foot G) r:= χ e r i - χ' e r (A.connects i)
def shelter (i:Page M): Orders (Foot G):= fullV S Y G Z s i-fullV S' Y G Z s' (A.connects i)
def bumpD (e r:ℕ) (i:Flap M): Packet (Foot G) r:= predicted S Y G Z s e r i - predicted S' Y G Z s' e r (A.fly i)
def alterB (e:ℕ)(i:Page M):ℝ:=biases (s i) e-biases (s' (A.connects i)) e
local notation "ψ"=> shelter S Y G Z s S' s' A
local notation "F"=> focusD S Y G Z s S' s' A
local notation "δ"=> alterB S s S' s' A -- order? S s S' s'
local notation "Ω₃"=> bumpD S Y G Z s S' s' A
variable (c:G.ColorIndex)(h:Known S Y G Z c s p)(h':Known S' Y G Z c s' p)
lemma minuses {T V:Packet (Foot G) 2}(h:costM T)(hp:costM V)(c:G.ColorIndex): Rules.token (T-V) c= Rules.token T c-Rules.token V c:= Rules.minus_shine h hp 2 (by omega) _ _ _
include h h'
lemma nimbus (hk:G.Simple)(he:0 < e)(hp:e≤p): Vessel S Y G Z s ψ r (F e (r+1)) e u:=by
 let T:= V_single S Y G Z s (u:=u) (r:=r) c hk he h hp; let T':=V_single S' Y G Z s' (u:=u) (r:=r) c hk he h' hp
 refine ⟨fun i=> comparison_token _ _ (T.branch _) (T'.branch _), fun i e r=> neg_s (V_s S Y G Z s i e r) (V_s S' Y G Z s' (A.connects i) e r),fun i=> neg_r (T.grade _) (T'.grade _),fun i j hj r=> subtracts (V_l S Y G Z s i j r) (V_l S' Y G Z s' (A.connects i) j r),fun i=> neg_s (T.matter _) (T'.matter _),fun i=>ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨T.duty _,T'.duty (A.connects i)⟩) (minus_amt ..),fun i hx=>?_,fun i hv=> congr_arg₂ (·-·) (T.lift _ hv) (T'.lift (A.connects i) hv),fun i=> ?_,fun i=>subtracts (T.successors _) (T'.successors _)⟩
 · subst r; let hK:= S'.pactP
   unfold focusD; have hz : amount (F e 2 i) 3≠⊤:= ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨sap_f (r:=1) S Y G Z s _ _,sap_f (r:=1) S' Y G Z s' _ (A.connects i)⟩) (minus_amt _ _ 3)
   exact Rules.wrinkles (Rules.minus_R (lane_p S Y G Z s _ hk he) (lane_p S' Y G Z s' _ hk he)) (Rules.star_paid hz (le_refl _) (bound_h _ _)) (show Rules.token (χ e 2 i-χ' e 2 (A.connects i)) c=0 from by rw [minuses G (sap_q S Y G Z s i) (sap_q S' Y G Z s' _),sap_t _ _ _ _ _ c i (h i).1 hp he,sap_t _ _ _ _ _ c _ (h' _).1 hp he,sub_self]) hk
 intro J;let q:=A.fly i; have hp' := T.levy i; let k:Packet (Foot G) (r+1):= fullV S' Y G Z s' q.prev e (r+1)-χ' e (r+1) q.prev
 have he':J= (fullV S Y G Z s i.prev e (r+1)-χ e (r+1) i.prev)-k:=by unfold J shelter focusD; rw [A.previous,Pi.sub_apply,Pi.sub_apply]; unfold k q; abel
 have hx:crest S Y G Z s i k:=by
    unfold k;rw [sap_levy S' Y G Z s' he]; by_cases ha:r=1
    · subst r;rw [peak_at]; exact worthy S Y G Z s S' s' i _ _ -- s' implicit
    rw [peak_dark _ (show r+1≠2 by omega),smul_zero]; rw [show (0:Packet _ (r+1))= _ from Eq.symm (sub_self (χ e _ i.prev))]; unfold crest; rw [inherits S Y G Z s i (sap_l S Y G Z s i.prev) (sap_l _ _ _ _ _ _), adopts S Y G Z s i (sap_l S Y G Z s i.prev) (sap_l _ _ _ _ _ _),sub_self,sub_self]
 rw [he']; exact ⟨subtracts hp'.1 (T'.levy (A.fly i)|>.1), wick_minus S Y G Z s i hp'.2 hx hp'.1 (T'.levy _|>.1)⟩
-- projection unary two sides
lemma agesR (i:Flap M)(he:0<e)(hp:e≤p): Rules.token (Ω₃ e 2 i) c = alterB S s S' s' A e i.next - alterB S s S' s' A e i.prev:=by
 unfold alterB bumpD;rw [minuses G (predicted_q S Y G Z s i) (predicted_q S' Y G Z s' _),predicts_v _ _ _ _ _ c i (h _).1 hp he,predicts_v _ _ _ _ _ c _ (h' _).1 hp he,A.previous, A.next];unfold increment;abel
lemma adjusting (i:Flap M)(he:0<e)(hp:e≤p): F e 2 i.next= burn S Y G (Ω₃ e 2 i) c i.next - Rules.token (predicted S' Y G Z s' e 2 (A.fly i)) c • (coil (S.scroll_j Y G i.next)-coil (S'.scroll_j Y G (A.connects i.next))):=by
 unfold focusD; rw [A.next]; unfold bumpD;let j:=A.fly i
 rw [normalized S Y G Z s c i (h _).1 he hp,normalized S' Y G Z s' c (A.fly i) (h' _).1 he hp]; unfold burn;rw [minuses G (predicted_q _ _ _ _ _ _) (predicted_q _ _ _ _ _ _),smul_sub,sub_smul]; abel
end duel
end V
end YM.RegulatorIR.Venture

import YM.RegulatorIR.Venture.Sap

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
local notation "A₀"=> curtain S Y G
local notation "A₁"=> pathL S Y G
local notation "N₀"=> lnk S G
local notation "T₀"=> S.scroll_j Y G
local notation "K₀"=> valley S Y G Z s
section Repair
local notation "T₁"=> S.payroll Y G Z s
local notation "U₁"=> S.devices Y G Z s
local notation "χ"=> chi S Y G Z s
local notation "ρ"=>predicted S Y G Z s
section white
variable (F: Page M→Scale) (c:G.ColorIndex)(j:Page M)
lemma token_cut (W:Packet (Foot G) 2)(c:G.ColorIndex) (p:Page M) (hv:Pupil.costM W) (d:ℝ): Rules.token (W-d • coil (T₀ p)) c= Rules.token W c-d:=by -- remove h
 let K:= coil (T₀ p); have he: Pupil.costM K:= full_r S Y G p; have hp: Pupil.costM (d • K):=by intro a b t n hn; apply ((he a b t n hn).mul_left d).congr; intro i; exact (mul_assoc ..).symm
 change Rules.token (W-d • K) c= _; unfold Rules.token; rw [Rules.minus_shine hv hp _ (by omega), Rules.smul_shine,show shine K 2 _ _ _=1 from Rules.kinetic (S.honored Y p).card c, mul_one]
variable (H:Tuned S Y G Z c s p j)
include H
lemma sap_t (h:e≤p)(ht:0<e) : Rules.token (χ e 2 j) c = 0:=by rw [chi,peak_at, token_cut S Y G ((T₁).bulk j _ _) c _ (cost_token S Y G Z s j _) _,H e h ht,sub_self]
omit H
lemma lane_p (hk:G.Simple)(ht:0<e): Rules (χ e 2 j):=by rw [chi,peak_at]; exact Rules.minus_R (ort_T S Y G Z s hk _ _ ht) (Rules.smul_R (ort_K S Y G Z s hk _) _)
lemma predicts_v (j:Flap M)(h:Tuned S Y G Z c s p (Flap.next j)) (he:e≤p)(hv:0<e): Rules.token (ρ e 2 j) c=increment s e j:=by
 unfold predicted;rw [peak_at]; apply (token_cut S Y G _ c _ (cost_token S Y G Z s _ _) _).trans; rw [h _ he hv];rfl
end white
variable {D:Choice M} {X':X→Type}
lemma normalized (c:G.ColorIndex)(f:Flap M)(H:Tuned S Y G Z c s p f.next)(he:0<e)(hv:e≤p): χ e 2 f.next= burn S Y G (ρ e 2 f) c f.next:=by rw [burn,predicts_v S Y G Z s c f H hv he]; unfold predicted chi increment; rw [peak_at, sub_smul]; abel
lemma sap_q (p:Page M) : costM (χ e 2 p):=Rules.star_paid (sap_f (r:=1) S Y G Z s 3 p) (le_refl _) (bound_h _ 3)
lemma predicted_q (f:Flap M) : costM (ρ e 2 f):=by
 unfold predicted; rw [peak_at]; let c:= biases (s f.prev) e;let t:=current_coat S Y G f.next 3; let T:= (T₁).bulk f.next e 2
 obtain ⟨a,hc,h⟩:=kernel_b S Y G Z s 3 f.next e 2
 have hp : Epoch.amount T 3 ≠⊤:= ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (by finiteness)) (earnsP T (S.l_p f.next) h)
 refine Rules.star_paid ?_ (le_refl 3) (bound_h _ 3); exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hp, ne_top_of_le_ne_top (ENNReal.mul_ne_top (a:=‖c‖ₑ) enorm_ne_top (show shareP G S 3 Y f.next≠⊤ from Epoch.assured _ _ _)) (amount_cap (scaled_p t c))⟩) (minus_amt ..)
lemma sap_levy (he:0<e)(f:Page M): fullV S Y G Z s f e (r+1)-χ e (r+1) f= biases (s f) e • Warm.peak (coil (T₀ f)) (r+1):=by rw [V_p _ _ _ _ _ _ he (by omega)]; unfold chi; abel
lemma fond_s (f:Page M)(he: r≠2) : χ e r f=(T₁).bulk f e r:= highR _ _ _ _ _ he f
-- build V.Estimator - only uv when both arrays true.T.Whi.K. Ready billed F rank all yes
lemma V_single (c:G.ColorIndex)(hk:G.Simple)(he:0<e)(H:Known S Y G Z c s p)(hp:e≤p) : Vessel S Y G Z s (fullV S Y G Z s) r (χ e (r+1)) e u:=by
 let v:= S; let X':= fullV S Y G Z s
 refine ⟨fun i=> badge _ _ _ _ _ _ _,fun i=> V_s _ _ _ _ _ _,fun i=>grammar _ _ _ _ _ _,fun i k _ r=> V_l _ _ _ _ _ i k r,fun i=> sap_h _ _ _ _ _ _ _ i,fun p=> sap_f _ _ _ _ _ _ _,fun i hx=>?_,fun i hv=>?_,fun i=>?_,fun i=> sap_l _ _ _ _ _ _⟩
 · subst r; exact Rules.wrinkles (lane_p _ _ _ _ _ i hk he) (sap_q S Y G Z s i) (sap_t S Y G Z s c i (H i).1 hp he) hk
 · rw [V_p _ _ _ _ _ _ he (by omega), highR _ _ _ _ _ (by omega)]
 intro D
 have hx:Limits D:= subtracts (V_l _ _ _ _ _ _ _ _) (sap_l S Y G Z s i.prev); refine ⟨hx, ?_⟩; unfold D; rw [sap_levy S Y G Z s he]; by_cases hr:r=1
 · subst r;rw [peak_at]; exact worthy S Y G Z s S s i _ _
 rw [peak_dark _ (by omega),smul_zero]; unfold crest valley river; -- simp proof
 have hp:firstChannel (S.opened G i.prev) (S.opened G i.next)=firstChannel (S.opened G i.prev) (S.opened G i.next):=rfl
 let V:= (U₁ i); rw [show offer _ (0:Packet (Foot G) (r+1))= _ from ?_]; -- zero
 · change V.pullI 0=_; rw [show V.pullI (r:=r+1) 0=0 from ?_]; ext1 x; simp [unfoldQ];
   simpa using! (pull_m V (r:=r+1) 0 0)
 ext1 w; simp [offer,Stalk.collect]
end Repair
end YM.RegulatorIR.Venture

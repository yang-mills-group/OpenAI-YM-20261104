import YM.RegulatorIR.Venture.Dusk

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

def chi (e r:ℕ)(p:Page M): Packet (Foot G) r:= (T₁).bulk p e r - biases (s p) e • (Warm.peak (coil (T₀ p)) r)
def predicted (e r:ℕ)(p:Flap M): Packet (Foot G) r:= (T₁).bulk p.next e r-biases (s p.prev) e • (Warm.peak (coil (T₀ p.next)) r)
def increment (e:ℕ)(p:Flap M):ℝ:= biases (s p.next) e - biases (s p.prev) e
local notation "χ"=> chi S Y G Z s
local notation "ρ"=> predicted S Y G Z s
lemma highP (h:r≠2)(f:Flap M): ρ e r f=(T₁).bulk f.next e r :=by rw [predicted,peak_dark _ h,smul_zero,sub_zero]
lemma highR (h:r≠2)(f:Page M): χ e r f=(T₁).bulk f e r:=by rw [chi,peak_dark _ h,smul_zero,sub_zero]
lemma sap_f (u:ℕ)(p:Page M): Epoch.amount (χ e (r+1) p) u ≠⊤:=by
 obtain ⟨a,h,H⟩:= kernel_b S Y G Z s u p e (r+1); have he:= earnsP (T₁|>.bulk p e (r+1)) (S.l_p p) H; have hp : Epoch.amount ((T₁).bulk p e (r+1)) u≠⊤:= ne_top_of_le_ne_top (by finiteness) he
 by_cases hz:r=1
 · subst r; unfold chi;rw [peak_at]; let c:= current_coat S Y G p u; exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hp,ne_top_of_le_ne_top (ENNReal.mul_ne_top enorm_ne_top (show shareP G S u Y p≠⊤ from assured _ _ _)) (amount_cap (scaled_p c _))⟩) (minus_amt ..)
 rw [highR _ _ _ _ _ (by omega)];exact hp
lemma sap_h (e r:ℕ)(p:Page M): IsSym (χ e r p):=by
 by_cases hp:r=2
 · subst r; unfold chi;rw [peak_at]; exact neg_s (symmetricV S Y G Z s p e 2) (symmetric_scale (coil_s _ (Stage.con S Y G Z s p|>.2.1)) _)
 rw [highR _ _ _ _ _ hp];exact symmetricV _ _ _ _ _ p e r
lemma sap_l (p:Page M): Limits (χ e (r+1) p):= bounds_from (earns (χ e (r+1) p) (u:=0) (S.l_p p) (sap_h _ _ _ _ _ _ _ _)) (ENNReal.mul_ne_top (sap_f _ _ _ _ _ _ _) (by finiteness))

def first_v (f:Flap M): Foot G↪ Foot G ⊕ Foot G:= (firstChannel (S.opened G f.prev) (S.opened G f.next)).native
def auxiliary (i j:ℕ)(w:Flap M):= Warm.mainL K (S.pactP w) G (Z _) i j + ∑ k∈(Finset.antidiagonal i).erase (i,0), biases (s w.prev) k.1 • Warm.mainR K (S.pactP w) G (Z _) (k.2+2) j
local notation "φ"=> auxiliary S G Z s -- shadow duplicate! rename next
def husk (i j:ℕ)(w:Flap M):= shedding (U₁ w).line ((U₁ w).jVac ((T₁).bulk w.prev)) i j
local notation "H₁"=> husk S Y G Z s
def rest (i j:ℕ)(w:Flap M):= auxiliary S G Z s i j w + H₁ i j w
local notation "Z₁"=> rest S Y G Z s
lemma coast_add (he:0<e)(j:ℕ)(p:Flap M): (U₁ p).addon e j= auxiliary S G Z s e j p + biases (s p.prev) e • (mainR K (S.pactP p) G (Z _) 2 j):=by
 rw [add_k _ _ _ _ _ _ _ he,Pi.add_apply,Finset.sum_apply,auxiliary]; simp_rw [Pi.smul_apply]; rw [← sum_erase_add _ _ (show (e,0)∈ antidiagonal e from by simp),add_assoc]
lemma background {r:ℕ}(f:Flap M): let J:= offer (first_v S G f) (Warm.peak (coil (T₀ f.prev)) r) + mainR K (S.pactP f) G (Z _) 2 r; Limits J∧ (U₁ f).pullI J= Warm.peak (coil (T₀ f.next)) r:=by -- remove e
 intro J; by_cases he:r=2
 · subst r; unfold J; simp_rw [peak_at]; exact portrays S Y G Z s f
 unfold J;rw [peak_dark _ he, paints S Y G Z f,peak_dark _ he, peak_dark _ he,add_zero]; rw [show offer (first_v S G f) (0:Packet _ r)=0 from ?_]
 · refine ⟨⟨0,by finiteness,fun _=>by simp⟩, ?_⟩; have ht:= pull_m (U₁ f) (r:=r) (0:Packet (KFoot G) r) 0; simpa using ht
 ext1 x;simp [offer,Stalk.collect]
lemma paidStamp (f:Flap M)(e:ℕ)(h:0<e)(r:ℕ)(hr:0<r) : let Q:= (U₁ f); let P:=Q.line; let Z':=Q.jVac (T₁|>.bulk f.prev); ceaseHeat P Z' false e r=(offer (first_v S G f) (χ e r f.prev)+Z₁ e r f)+biases (s f.prev) e • (offer (first_v S G f) (Warm.peak (coil (T₀ f.prev)) r)+ Warm.mainR K (S.pactP f) G (Z _) 2 r):=by
 intro Q P Z'
 unfold ceaseHeat;rw [first_payment, logHeat_first,if_neg (show ¬(r=0∧false=false) by omega)]
 let v:= first_v S G f;let A:= auxiliary S G Z s e r f
 change (offer v (_:Packet _ r)+(U₁ f).addon e r)+ H₁ e r f= _ -- ensure manageable
 rw [coast_add _ _ _ _ _ h]; unfold chi rest; rw [smul_add,offer_diff,Sources.scaleO]; abel
lemma background_f (f:Flap M)(h:0<e)(hh:0<r): Limits (Z₁ e r f):=by
 let v:= U₁ f; let T:= (T₁).bulk f.prev;let L:=χ e r f.prev; have hx:= cease_k S Y G Z s f e r; let X:=v.jVac T; let Ψ:=ceaseHeat v.line X false e r; let b:=biases (s f.prev) e;let F:= offer (first_v S G f) (Warm.peak (coil (T₀ f.prev)) r)+ Warm.mainR K (S.pactP f) G (Z _) 2 r
 have H:Ψ=(offer (first_v S G f) L+ Z₁ e r f)+b • F:= paidStamp S Y G Z s f e h r hh -- Y notation shadow use rename
 have ht: Z₁ e r f= (Ψ-b • F)-offer (first_v S G f) L:=by rw [H];abel
 rw (occs:=.pos [1]) [ht]; refine subtracts (subtracts hx (tilt_l (background S Y G Z s f|>.1) b)) (offerL (?_) _)
 unfold L; cases r with
 | zero=>omega
 | succ r=> exact sap_l S Y G Z s _
lemma reprised (f:Flap M)(h:0<e) : ρ e (r+1) f= valley S Y G Z s f (χ e (r+1) f.prev)+(U₁ f).pullI (Z₁ e (r+1) f):=by
 let D:= U₁ f; have hv : (T₁).bulk f.next= D.pure ((T₁).bulk f.prev):= ((T₁).step_v f).symm
 unfold predicted;rw [hv, GridStep.pure,if_neg (by omega)]; rw [show ceaseHeat D.line _ false e (r+1)= _ from paidStamp S Y G Z s f e h (r+1) (by omega)];
 obtain ⟨hx,h⟩:=background S Y G Z s (r:=r+1) f; have ht:= background_f S Y G Z s (e:=e) f (show 0<e by assumption) (r:=r+1) (by omega); have hp:= offerL (sap_l (e:=e) (r:=r) S Y G Z s f.prev) (first_v S G f); have he:= (flits S Y G Z s f).1;
 rw [pull_a D he (add_l hp ht) (tilt_l hx _), pull_a D he hp ht,pull_m,h,add_sub_cancel_right];rfl
end Repair
end YM.RegulatorIR.Venture

import YM.RegulatorIR.Venture.Program

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
section Stabilize
-- projection plus paid drift cost.Cover cut. A construction.$C.Next$ pays projection
-- when grade2. Q.B mask.Clipped.
variable (C:Scripted S Y G Z p u B γ) {T:Page M→Orders (Foot G)} {F:Page M→Packet (Foot G) (r+1)}
variable (D:Vessel S Y G Z s T r F e u)
include C D
-- in Currency.M.Point output charge.H.Cost.K.Work. Caller computes Projection fees.Function α.Pre.Source.
lemma damp_s (hi:1≤r)(h:r+1≤e+2)(hp:e≤p)(ht:θ<γ)(hx:0≤θ)(hQ:B.More Q θ) (hv:∀ i<e,∀ j,0<j→j ≤ i+2→VacDay Q B.age_t (N₀ u) fun w=> T w i j) (hF: VacDay (Q∘Page.opening M) (B.age_t.us (Page.opening M)) (N₀ u∘ Page.opening M) (fun w=>F (Page.opening M w))) (R: Flap M→Packet (Foot G) (r+1))(H:VacDay (Q∘Flap.prev) B.age_f (N₀ u∘ Flap.next) (fun i=> R i-K₀ i (F i.prev))) (Hz:∃ a,Carry B.age_f (Q∘Flap.prev) a ∧∀ i:Flap M,amount (F i.next) u ≤ amount (R i) u*(1+shareP G S u Y i.next)+a i): VacDay Q B.age_t (N₀ u) F ∧ Carry B.age_f (Q∘Flap.prev) (fun i=> amount (R i) u):=by
 obtain ⟨a,hA,Ha⟩:=Hz; obtain ⟨b,hb,Hb⟩:= rive_v S Y G Z s C D hi h hp (fun i j k l p=> hv i j k l p) H
 let Q₁:= fun i=>amount (F i) u
 let f(i:Flap M):=1+League.shareP G S u Y i.next
 have H₁: Carry B.age_t Q Q₁:=by
    refine B.damper Q _ θ γ C.funding.capital ht hx hQ (Carry.add (hb.mul_right (Poly.add (Poly.oneQ _) (shares_up S Y G Z C))) hA) (amount_profits (D:=fun w=> S.l (Page.opening M w)) (fun w=> S.l_p _) hF) (fun i=> ?_)
    have he:= C.cold r hi (by omega) i
    apply (Ha i).trans ((add_le_add_left (mul_le_mul_left (Hb i) _) (a i)).trans ?_); change (_+_)* f i+ a i≤ _+ (b i*f i+_)
    rw [add_mul, add_assoc]; apply add_le_add_left; rw [mul_right_comm]; exact mul_le_mul_left he _
 exact ⟨bonds_v (fun i: Page M=>S.l_p i) H₁ D.matter, Carry.mono (Carry.add (Carry.mul_left (poll_t _ _ _ _ C r) (H₁.us Flap.prev)) hb) Hb⟩
end Stabilize
-- Token norm
lemma cash_v (T:Packet (Foot G) 2)(c:G.ColorIndex)(h:2≤u): ‖Rules.token T c‖ₑ≤ amount T u:= Rules.token_price h (bound_h T u) c
lemma minus_amt {X:Type}(T U:Packet (Long X) (r+1))(u:ℕ): amount (T-U) u ≤ amount T u+amount U u:=amount_cap (fun i=> (quota_sub (Momentum.anchored i T) _ _).trans (add_le_add (bound_h T u i) (bound_h U u i)))
-- collar projection at next. Caller pays optional step.
def burn (T:Packet (Foot G) 2)(c:G.ColorIndex)(i:Page M):= T-Rules.token T c • coil (T₀ i)
lemma coating (T:Packet (Foot G) 2)(i:Page M)(c:G.ColorIndex)(H:2≤u): amount (burn S Y G T c i) u ≤ amount T u *(1+ shareP G S u Y i) :=by
 unfold burn; rw [mul_add, mul_one]
 apply (minus_amt _ _ u).trans; apply add_le_add_right; apply le_trans (amount_cap (scaled_p (current_coat S Y G i u) _)); exact mul_le_mul_left (cash_v G T c H) _
-- compiler histories traces 
end YM.RegulatorIR.Venture

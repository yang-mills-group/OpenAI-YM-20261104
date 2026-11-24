import YM.RegulatorIR.Venture.Style

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
local notation "N₁"=> drifted S G
local notation "S₁"=> B.age_f
local notation "β"=>B.age_t
variable (H:Scripted S Y G Z p u B γ)(hg:0<γ)(c:G.ColorIndex) (hk:G.Simple)
include H
lemma K_r : Workday β (N₀ u) (fun w=> coil (T₀ w)):=by
 apply plain_r;apply bonds_v (T:=fun w=> coil (T₀ w)) (fun w=> S.l_p w); exact Carry.regular (H.funding.currency.mono fun i=> amount_cap (current_coat _ _ _ _ _)); exact fun w=> coil_s _ (Stage.con S Y G Z (fun _=> dawn.scale) w).2.1
omit H in
lemma dawnGrant (ht:∀ j<e,Poly β fun w=>‖biases (s w) j‖ₑ)(he:0<e)(hr:2 ≤ r) (hv:r≤ e+2): Workday (B.age_t.us (Page.opening M)) (N₀ u∘ Page.opening M) (fun w=> χ e r (Page.opening M w)):=by -- H not used!
 by_cases hx:r=2
 · subst r; simp_rw [chi,peak_at,warmedUp S Y G Z s _ e he,sub_self];exact Workday.zeroQ
 let f:= Page.opening M;let V:= many (beginF G) r r
 have hp(w:X):χ e r (f w)=biases (s (f w)) (e+2-r) • V:=by rw [highR _ _ _ _ _ hx]; exact primary_high _ (Circuit.serene G s w) he hr hv
 have h: Workday (B.age_t.us f) (N₀ u ∘ f) (fun _=>V):= ⟨_,Poly.standard _ (handle_fin G r r u),fun x=> handled _ r r _ (S.l_p (f x))⟩;convert (Workday.smul (c:=fun w=>biases (s (f w)) (e+2-r)) h ((ht _ (by omega)).us f)) using 1; ext1 i; exact hp i
variable (Y':Known S Y G Z c s p)
include c hk hg Y'
lemma chartered (hv:∀ i j, Earlier e (r+1) i j→ Workday β (N₀ u) (fun w=>(T₁).bulk w i j))(ht:∀ i<e,Poly β fun w=>‖biases (s w) i‖ₑ)(hx:0< e)(h:r+1≤e+2)(h0:1≤ r)(hp:e≤p) : Workday β (N₀ u) (χ e (r+1))∧ Poly S₁ (fun i=> amount (ρ e (r+1) i) u):=by
 let b:= β; let D:= V_single (r:=r) S Y G Z s (u:=u) c hk hx Y' hp
 have hM :B.More (fun _=>1) 0:=fun i=>by simp [Marked.coin]
 have hh:VacDay (1: Flap M→ℝ≥0∞) S₁ (N₁ u) (rest S Y G Z s e (r+1)):= plain (fare_z _ _ _ _ _ H hp (by omega) h hv ht)
 suffices HE : VacDay 1 B.age_t (N₀ u) (χ e (r+1))∧ Carry S₁ 1 (fun i=>amount (ρ e (r+1) i) u) from ⟨plain_r HE.1, HE.2.admit (Poly.oneQ _)⟩
 refine damp_s S Y G Z s H (B:=B) D h0 h hp hg (le_refl 0) hM ?_ (plain (dawnGrant S Y G Z s ht hx (by omega) h)) (ρ e (r+1)) ?_ ?_
 · intro i hi j hj _
   by_cases Hj:i=0
   · subst i; by_cases he:j=2
     · subst j;simp_rw [V_i];exact plain (K_r S Y G Z H)
     simp_rw [V_at _ _ _ _ _ _ he]; exact zero_r
   simp_rw [fun w:Page M=> V_p S Y G Z s w (show 0 < i by omega) hj]; exact plain (hv i j (Or.inl hi))
 · convert task S Y G Z s H (Q:=fun _=>1) hh using 1 <;> first|rfl |  (ext1 w; rw [reprised S Y G Z s w hx]; abel)
 refine ⟨0,Carry.zeroQ _,?_⟩; intro i; by_cases hr:r=1
 · subst r; rw [Pi.zero_apply,add_zero,normalized S Y G Z s c i (Y' i.next).1 hx hp];exact coating _ _ _ _ _ _ (by have hp:=H.funding.depth;omega)
 rw [highR S Y G Z s (show r+1 ≠ 2 by omega), highP S Y G Z s (show r+1≠2 by omega),Pi.zero_apply,add_zero]; exact le_mul_of_one_le_right bot_le le_self_add
end Repair
end YM.RegulatorIR.Venture

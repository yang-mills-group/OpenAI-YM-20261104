import YM.RegulatorIR.Venture.Signal

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

local notation "ψ"=> shelter S Y G Z s S' s' A
local notation "F"=> focusD S Y G Z s S' s' A
local notation "δ"=> alterB S s S' s' A -- order? S s S' s'
local notation "Ω₃"=> bumpD S Y G Z s S' s' A
-- polynomial authorization shape for both. lighter B.En.Critical.Ratio.P
variable (D:Choice M) (D':Choice M')
variable (R: Remit S Y G Z S' A D D' p u B B' θ γ)
local notation "v"=>Reserve.maskB B θ
local notation "l"=> Reserve.peak_M B θ
include R
local notation "N₂"=> drifted S G
local notation "C₁"=> A.fly
variable (T:∀ i≤p,∀ r,Workday B.age_t (lnk S G u) (fun w=>(S.payroll Y G Z s).bulk w i r))(Tb:∀ i≤p,Poly B.age_t fun x=> ‖biases (s x) i‖ₑ)
variable (T':∀ i ≤ p,∀ r,Workday B'.age_t (lnk S' G u) (fun w=> (S'.payroll Y G Z s').bulk w i r))(Tb':∀ i≤p,Poly B'.age_t (fun w=> ‖biases (s' w) i‖ₑ))
variable (c:G.ColorIndex)(hk:G.Simple)(H:Known S Y G Z c s p) (H':Known S' Y G Z c s' p)
include H H' hk T T' Tb Tb'
def Δbody (i j:ℕ) (w:Page M) : Packet (Foot G) j:= (U₀).bulk w i j - (U₁).bulk (A.connects w) i j
local notation "Δ"=> Δbody S Y G Z s S' s' A
lemma joins_high (he:e≤p)(hv:0<e)(h:∀ i<e,Carry β v fun j=> ‖δ i j‖ₑ)(hp:∀ i<e,∀ j,VacDay v β (Ω₁ u) (Δ i j)):∀ i j,Earlier e 2 i j→ VacDay v β (Ω₁ u) (Δ i j):=by
 suffices h :∀ n:ℕ,∀ j,2 < j→ e+3-j=n → VacDay v β (Ω₁ u) (Δ e j) by
    rintro i j (H|⟨rfl,ht⟩);exact hp _ H _;exact h _ j ht rfl
 intro n; induction n using Nat.strong_induction_on with
 | _ n ih=>
    intro j hj hJ; by_cases Z':j≤e+2
    · cases j with
      | zero=>omega
      | succ j=>
       have hp':∀ i r,Earlier e (j+1) i r→ VacDay v β (Ω₁ u) (Δ i r):=by
          rintro i r (h|⟨h,hp⟩); exact hp _ h _;rw [h]; exact ih _ (show e+3-r<n by omega) _ (by omega) rfl
       convert (contract_d S Y G Z s S' s' A D D' R T Tb T' Tb' c hk H H' (r:=j) (by omega) hv he Z' h hp').1 using 1; ext1 w; unfold Δbody focusD; rw [highR _ _ _ _ _ (Ne.symm (Nat.ne_of_lt hj)),highR _ _ _ _ _ (Ne.symm (Nat.ne_of_lt hj))]
    have he(w:Page M) : Δ e j w=0:=by
       have hp :(U₀).bulk w e j=0:= Classical.not_not.mp (fun hp=> Z' (stem_h _ _ _ _ _ w _ j hp).2)
       have hV :(U₁).bulk (A.connects w) e j=0:= Classical.not_not.mp (fun hp=> Z' (stem_h _ _ _ _ _ _ _ j hp).2)
       unfold Δbody; rw [hp,hV,sub_self]
    rw [funext he]; exact VacDay.zero_r
variable (hS:∀ p,s (D.choose p)=dawn.scale) (hS':∀ p,s' (D'.choose p)=dawn.scale)
include hS hS'
lemma brink (he:e≤p)(hv:0<e)(hb:∀ i<e,Carry β v fun j=> ‖δ i j‖ₑ)(ht:∀ i<e,∀ j, VacDay v β (Ω₁ u) (Δ i j)) : Carry β v (fun j=>‖δ e j‖ₑ) ∧ ∀ j,VacDay v β (Ω₁ u) (Δ e j):=by
 have hx:= joins_high S Y G Z s S' s' A D D' R T Tb T' Tb' c hk H H' he hv hb ht
 obtain ⟨h,hp⟩:= contract_d S Y G Z s S' s' A D D' R T Tb T' Tb' c hk H H' (r:=1) le_rfl hv he (by omega) hb hx
 have hV:Carry β v fun i=>‖δ e i‖ₑ:=by
    refine B.license D (δ e) v R.beam (Reserve.medium B D R.beam θ R.θp) (fun w=>by unfold alterB;rw [R.spot,hS,hS',sub_self]) ?_
    apply hp.mono; intro i;dsimp only; rw [← show Rules.token (Ω₃ e 2 i) c= _ from agesR S Y G Z s S' s' A c H H' i hv he]; exact cash_v G _ _ (by have hp:=R.f.funding.depth;omega)
 refine ⟨hV,fun r=>?_⟩; by_cases ht:2 < r
 · exact hx _ _ (Or.inr ⟨rfl,ht⟩)
 rcases le_or_gt r 1 with hp|hp
 · interval_cases r
   · exact void_r
   have h(i:Page M) : Δ e 1 i=0:=by unfold Δbody; rw [stated_s S Y G Z s _ e hk,stated_s S' Y G Z s' _ e hk,sub_self]
   rw [funext h];exact zero_r
 have hr:r=2:=by omega
 subst r
 -- recover T=F + δ*K_A + b'*(K_A-K_B)
 have hx: Poly β (fun i=> ‖biases (s' (A.connects i)) e‖ₑ):= renewed (Poly.us (Tb' e he) A.connects) R.width
 let f:= h.add ((VacDay.rents (K_r S Y G Z R.f) hV).add (VacDay.smulP (coat_v S Y G Z S' A D D' R) hx))
 convert f using 1;ext1 i; let V:= S'.scroll_j Y G (A.connects i);
 change _=F e 2 i+ ((δ e i) • Axial.coil _+ biases (s' _) e • (Axial.coil _-Axial.coil V)); unfold Δbody focusD chi alterB; rw [peak_at,peak_at,sub_smul,smul_sub];unfold V; abel
lemma fullD : ∀ e≤p, Carry β v (fun j=>‖δ e j‖ₑ)∧∀ j,VacDay v β (Ω₁ u) (Δ e j):=by
 intro e; induction e using Nat.strong_induction_on with
 | _ e ih=>
    intro he; by_cases ht:0< e
    · exact brink S Y G Z s S' s' A D D' R T Tb T' Tb' c hk H H' hS hS' he ht (fun i hi=>(ih i hi (hi.le.trans he)).1) (fun i hi=>(ih i hi (hi.le.trans he)).2)
    have hp:e=0:=by omega
    subst e;constructor
    · unfold alterB;simp_rw [Calibration.returns,sub_self,enorm_zero];exact Carry.zeroQ v
    intro j; unfold Δbody; simp_rw [fun w:Page M=>vacuum_lo _ (stem_h S Y G Z s w),fun w:Page M'=> vacuum_lo _ (stem_h S' Y G Z s' w),sub_self];exact VacDay.zero_r
omit T Tb T' Tb'
theorem evolution_d : ∀ e≤p, Carry β v (fun j=>‖δ e j‖ₑ)∧∀ j,VacDay v β (Ω₁ u) (Δ e j):=by
 have ht:0<γ:= lt_of_le_of_lt R.θp R.θv
 have hp:= solstice S Y G Z s R.f ht c hk H D R.beam hS; have hP:= solstice S' Y G Z s' R.s ht c hk H' D' R.wing hS'
 exact fullD S Y G Z s S' s' A D D' R (fun i hi=> (hp i hi).1) (fun i hi=>(hp i hi).2) (fun i hi=>(hP i hi).1) (fun i hi=>(hP i hi).2) c hk H H' hS hS'
end duel
end V
end YM.RegulatorIR.Venture

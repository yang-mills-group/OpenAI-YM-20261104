import YM.RegulatorIR.Venture.Solo

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
variable (H:Scripted S Y G Z p u B γ)(hg:0<γ)(c:G.ColorIndex)(hk:G.Simple)
variable (F:Known S Y G Z c s p)(D:Choice M)(hD:∀ w,B.peak (D.choose w)=0)(hF:∀ w,s (D.choose w)=dawn.scale)
include F H hg hk
-- same-order ranks ≥3 first
lemma rehearsed (T:∀ i<e,∀ j,Workday β (N₀ u) fun w=> (T₁).bulk w i j)(Q:∀ i<e,Poly β (fun w=>‖biases (s w) i‖ₑ))(he:e≤p)(hv:0<e) :∀ i j,Earlier e 2 i j→ Workday β (N₀ u) fun w=>(T₁).bulk w i j:=by
 suffices hp :∀ n:ℕ,∀ i, e+3-i=n→ 2 < i → Workday β (N₀ u) (fun w=>(T₁).bulk w e i) by
    rintro i j (h|⟨h,hv⟩); exact T i h j; subst i; exact hp _ j rfl hv
 intro n;induction n using Nat.strong_induction_on with
 | _ n ih=>
    intro i hi hj; by_cases hp : i≤ e+2
    · cases i with
      | zero=>omega
      | succ i=>
       have h: ∀ k j,Earlier e (i+1) k j→ Workday β (N₀ u) fun w=> (T₁).bulk w k j:=by
          rintro k j (h|⟨h,hj'⟩);exact T k h j;rw [h];exact ih _ (show e+3-j<n from by omega) _ rfl (by omega)
       have hK:=(chartered S Y G Z s H hg c hk F h Q hv hp (show 1≤ i by omega) he).1
       convert hK using 1; ext1 j; exact (highR S Y G Z s (Ne.symm (Nat.ne_of_lt hj)) j).symm
    have ht(w): (T₁).bulk w e i=0:= Classical.not_not.mp (fun hp'=>hp ((stem_h _ _ _ _ _ _ _ _ hp').2))
    simp_rw [ht];exact Workday.zeroQ
include hD hF
lemma midnight (T:∀ i<e,∀ j,Workday β (N₀ u) fun w=> (T₁).bulk w i j)(Q:∀ i<e,Poly β (fun w=>‖biases (s w) i‖ₑ))(he:e≤p)(hv:0<e): (∀ r,Workday β (N₀ u) (fun w=>(T₁).bulk w e r))∧ Poly β (fun w=>‖biases (s w) e‖ₑ):=by
 let K:= rehearsed S Y G Z s H hg c hk F T Q he hv
 obtain ⟨h,hp⟩:=chartered (r:=1) S Y G Z s H hg c hk F K Q hv (by omega) (by omega) he
 let E(w:Page M):=biases (s w) e
 have he :Poly β (fun i=> ‖E i‖ₑ) :=by
    have hB: Marked.Balancer D (fun _=>1):=⟨fun _ _=>le_rfl,fun _ _=>le_rfl⟩
    apply Carry.admit (B.license D E _ hD hB ?_ ?_) (Poly.oneQ _)
    · intro v; unfold E; rw [hF]; cases e with
      | zero=>omega
      | succ j=>exact Calibration.starts j
    apply Carry.regular; apply hp.mono; intro i;change ‖increment s e i‖ₑ≤_
    rw [← predicts_v _ _ _ _ _ c i (F i.next).1 (by assumption) hv]; exact cash_v _ _ _ (by have ht:=H.funding.depth;omega)
 refine ⟨?_,he⟩
 intro r; by_cases hx:2 = r
 · subst r;convert h.add (Workday.smul (K_r S Y G Z H) E he) using 1; ext1 i; change _= χ e 2 i + E i • _;rw [chi,peak_at, show E i= biases _ _ from rfl,sub_add_cancel]
 rcases le_or_gt r 1 with hr|hr
 · interval_cases r;exact plain_r void_r; simp_rw [fun p:Page M=> stated_s S Y G Z s p e hk];exact Workday.zeroQ
 exact K _ r (Or.inr ⟨rfl,by omega⟩)
-- export simultaneous finite precision matching
lemma solstice : ∀ e≤p, (∀ r,Workday β (N₀ u) fun w=>(T₁).bulk w e r) ∧ Poly β fun w=>‖biases (s w) e‖ₑ :=by
 intro e; induction e using Nat.strong_induction_on with
 | _ e ih=>
    intro he; by_cases hx: e=0; swap
    · exact midnight S Y G Z s H hg c hk F D hD hF (fun i hi=> (ih i hi (hi.le.trans he)).1) (fun i hi=> (ih i hi (hi.le.trans he)).2) he (by omega)
    subst e; constructor
    · intro r;simp_rw [fun p:Page M=> vacuum_lo ((T₁).bulk p) (stem_h S Y G Z s p)]; exact Workday.zeroQ
    simp_rw [Calibration.returns,enorm_one];exact Poly.oneQ _
omit hD F hF
lemma dome (t:Tent M)(D:Choice M)(hD:∀ w,B.peak (D.choose w)=0)(H':Notebook S Y G Z c D t p): (∀ i ≤ p,∀ r,Workday β (N₀ u) (fun w=> ((S.payroll Y G Z (sheet t)).bulk w i r)))∧∀ i≤p, Poly β (fun w=>‖biases (sheet t w) i‖ₑ):=by
 have ht:= solstice S Y G Z _ H hg c hk H'.clean D hD (fun w=>congr_arg Feeds.scale (H'.reference w)); exact ⟨fun i hi=> (ht i hi).1,fun i hi=>(ht i hi).2⟩
end Repair
end YM.RegulatorIR.Venture

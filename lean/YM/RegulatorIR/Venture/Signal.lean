import YM.RegulatorIR.Venture.Coffee

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
lemma stepDown (i:Flap M): v i.next ≤ v i.prev:=by
 unfold Reserve.maskB; rw [B.mark_P,show i.next.bindW=i.prev.bindW from rfl]; gcongr; exact R.θp; exact (le_add_of_nonneg_right (B.rise i).le)
-- projection rent comes from both K2 and predicted RHS'. T' dollars at both ancestors.
lemma prodK : let k(i: Flap M):=coil (S.scroll_j Y G i.next)-coil (S'.scroll_j Y G (A.connects i.next)); Carry α (v ∘ Flap.prev) (fun i=> Epoch.amount (k i) u):=by
 intro k; have hp:= amount_profits (D:=S.l) (u:=u) (S.l_p) (coat_v S Y G Z S' A D D' R)
 let a:= B.age_t.us Flap.next; have hK:= Epoch.refreshed (hp.us Flap.next) (B.utilizes R.f.funding.capital)
 exact Carry.charge hK (Carry.mono (Carry.unit B.age_f (v ∘ Flap.prev)) (fun i=>stepDown S Y G Z S' A D D' R i))
variable (c:G.ColorIndex)(hk:G.Simple) (H:Known S Y G Z c s p)(H': Known S' Y G Z c s' p)
local notation "Q₁"=> B'.age_t
include T' Tb' hk H'
lemma stellar_r (he:0<e)(ht:e≤p): Poly α (fun i=> ‖Rules.token (predicted S' Y G Z s' e 2 (A.fly i)) c‖ₑ) :=by
 have h:= (chartered (r:=1) S' Y G Z s' R.s (lt_of_le_of_lt R.θp R.θv) c hk H' (fun i j h=>T' _ ((nearer h).trans ht) j) (fun i hi=> Tb' i (hi.le.trans ht)) he (by omega) (by omega) ht).2
 refine (renewed (Poly.us h A.fly) (flightS _ _ A R.width)).mono ?_; exact fun i=> cash_v _ _ _ (by have hp:= R.f.funding.depth;omega)
include H
lemma magnet (h:0<e)(he:e≤p) : ∃ a,Carry α (v∘Flap.prev) a ∧∀ i:Flap M, Epoch.amount (F e (r+1) i.next) u≤ Epoch.amount (Ω₃ e (r+1) i) u * (1+shareP G S u Y i.next)+ a i:=by
 by_cases hr:r=1
 · subst r; have hp:=stellar_r S Y G Z S' s' A D D' R T' Tb' c hk H' h he -- parameters s note
   refine ⟨_,Carry.mul_left hp (prodK S Y G Z S' A D D' R),fun i=> ?_⟩
   rw [show F e (1+1) i.next= _ from adjusting S Y G Z s S' s' A c H H' i h he]; apply (minus_amt ..).trans; refine add_le_add (coating _ _ _ _ _ _ (by have hx:=R.f.funding.depth;omega)) (amount_cap (scaled_p (bound_h _ u) _)) -- n:= unknown
 have hh(i) : F e (r+1) (Flap.next i)= Ω₃ e (r+1) i:=by
    unfold focusD bumpD; have h:r+1≠2:=by omega
    rw [highR _ _ _ _ _ h,highR _ _ _ _ _ h,highP _ _ _ _ _ h,highP _ _ _ _ _ h, A.next]
 exact ⟨_,Carry.zeroQ _,fun i=> by rw [hh]; simp only [Pi.zero_apply,add_zero]; exact le_mul_of_one_le_right bot_le le_self_add⟩
omit hk H H'
include T Tb
lemma engulfs (hp:e≤p): VacDay (v ∘ Page.opening M) (B.age_t.us (Page.opening M)) (Ω₁ u ∘ Page.opening M) (fun w=> F e r (Page.opening M w)):=by
 let i := Page.opening M
 have hP:VacDay 1 β (Ω₁ u) (fun w:Page M=> F e r w):= VacDay.sub (plain (coil_p S Y G Z s R.f (T e hp _) (Tb e hp))) (plain (creep S G S' A R.measure R.width (coil_p S' Y G Z s' R.s (T' e hp _) (Tb' e hp))))
 have hv(x:X): Marked.backward D (i x):= Nat.zero_le _
 rw [show v∘Page.opening M=1 from ?_]
 exact hP.once i
 ext1 y;change ENNReal.ofReal (Real.exp ((B.peak (i y)- min (B.peak (i y)) 0)*θ))=1; rw [min_eq_left (B.debit D R.beam (i y) (hv y)),sub_self,zero_mul,Real.exp_zero, ENNReal.ofReal_one]
-- contracts Ω at least moment at all e and local Ly retention. No physical world assumption.
include H H' hk
lemma contract_d (hx:1≤r)(he:0<e)(hp:e≤p)(hb:r+1≤e+2)(hZ:∀ i<e,Carry β v fun p=> ‖δ i p‖ₑ)(hT:∀ i j, Earlier e (r+1) i j→ VacDay v β (Ω₁ u) (fun p=>(U₀).bulk p i j-(U₁).bulk (A.connects p) i j)):
 VacDay v β (Ω₁ u) (F e (r+1))∧ Carry α (v ∘ Flap.prev) (fun i=>Epoch.amount (Ω₃ e (r+1) i) u):=by
 refine damp_s S Y G Z s R.f (nimbus S Y G Z s S' s' A c H H' hk he hp) hx hb hp R.θv R.θp (Reserve.shadow _ R.θp) ?_ (engulfs S Y G Z s S' s' A D D' R T Tb T' Tb' hp) _ (brew S Y G Z s S' s' A D D' R T Tb T' Tb' he hp hb hx hZ hT) (magnet S Y G Z s S' s' A D D' R T' Tb' c hk H H' he hp)
 intro i hi j hj hp; unfold shelter; simp_rw [Pi.sub_apply];by_cases h:i=0
 · subst i; by_cases he:j=2
   · subst j; simp_rw [V_i];exact coat_v _ _ _ _ _ _ _ _ R
   simp_rw [V_at _ _ _ _ _ _ he,sub_self];exact zero_r
 simp_rw [V_p _ _ _ _ _ _ (show 0 < i by omega) hj];exact hT _ _ (Or.inl hi)
end duel
end V
end YM.RegulatorIR.Venture

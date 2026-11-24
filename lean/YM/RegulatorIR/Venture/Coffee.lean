import YM.RegulatorIR.Venture.Horn

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
omit R in
lemma nearer {i j:ℕ}(h:Earlier e r i j): i ≤ e:=by unfold Earlier at h;omega
include T Tb
-- transfer Weighted
include T' Tb'
lemma paid_r (he: e ≤ p)(h: r+1 ≤ e+2)(ht:1≤r) : let a:=rest S Y G Z s e (r+1); let b:=rest S' Y G Z s' e (r+1)
                                   Workday α (N₂ u) a∧Workday α (N₂ u) (fun i=> b (C₁ i)) :=by
 intro a b; refine ⟨fare_z S Y G Z s R.f he (by omega) h ?_ (fun _ hz=> Tb _ (hz.le.trans he)),draisin S G S' A R.measure R.width (fare_z S' Y G Z s' R.s he (by omega) h ?_ (fun _ hz=> Tb' _ (hz.le.trans he)))⟩
 exact fun i j hx=>T _ ((nearer hx).trans he) j
 exact fun i j hx=>T' _ ((nearer hx).trans he) j
lemma spark (he:e≤p)(h:r+1 ≤e+2)(hi:1≤r)(H:∀ i<e, Carry β v (fun p=>‖δ i p‖ₑ))(Hp:∀ i j,Earlier e (r+1) i j→ VacDay v β (Ω₁ u) (fun p=> (U₀).bulk p i j-(U₁).bulk (A.connects p) i j)):
 VacDay (v ∘ Flap.prev) α (N₂ u) (fun i=> rest S Y G Z s e (r+1) i - rest S' Y G Z s' e (r+1) (C₁ i)):=by
 let K:= over_k S Y G Z s S' s' A D D' R he (show 2 ≤r+1 by omega) H Hp
 unfold rest; simp_rw [add_sub_add_comm]; refine VacDay.add (coast_k S Y G Z s S' s' A D D' R he (show r+1 ≤p+2 by omega) H) ?_;obtain ⟨h₁,h₂⟩:= beam_shapes S Y G Z s S' s' A R.measure R.width R.f R.s
 refine restoration_t h₁ (fun i=> joint_h S Y G Z s i) ?_ h₂ (lines_d _ _ _ _ _ _ _ _ _ _ R) (fun i=> joint_h S' Y G Z s' _) ?_ K
 · exact joints S Y G Z s R.f he (by omega) (fun i j h'=> T _ ((nearer h').trans he) j) (fun i ht=>Tb i (ht.le.trans he))
 intro i j hv; exact draisin S G S' A R.measure R.width (joints S' Y G Z s' R.s he (by omega) (fun i j h'=>T' _ ((nearer h').trans he) j) (fun i ht=> Tb' _ (ht.le.trans he)) i j hv)
omit T Tb T' Tb'
lemma hopes_d {Z' W:Flap M→Packet (KFoot G) r} (T: Workday α (N₂ u) Z') (h:Workday α (N₂ u) W)(hp: VacDay (v ∘ Flap.prev) α (N₂ u) (fun i=> Z' i-W i)):
 VacDay (v ∘ Flap.prev) α (fun i=>Ω₁ u i.next) (fun i=> (A₀ i).pullI (Z' i)-(A₁ (C₁ i)).pullI (W i)):=by
 have hh:= draft_v (P:=fun i=> (A₀ i).driftL) (R:=fun i=>(A₁ (C₁ i)).driftL) T h (forecast_k S Y G Z s R.f) (draisinL _ _ _ A R.measure R.width (forecast_k _ _ _ _ _ R.s)) (beams_d S Y G Z s S' s' A D D' R) hp
 obtain ⟨c,h,H⟩:= hh; refine ⟨_,h,fun i=>?_⟩
 let p:= lastChannel (S.opened G i.prev) (S.opened G i.next); let V:= N₂ u i
 exact local_crop p.native (T:= Packet.draft (A₀ i).driftL (Z' i)-Packet.draft (A₁ (C₁ i)).driftL (W i)) (A:=Tariff.native _ (S.l_p i.next) u) (peak_o G (S.l i.prev) (S.l i.next)) (H i)
omit R in
lemma coil_p {R:Marked M}(Z₁:Scripted S Y G Z p u R γ) (H:Workday R.age_t (Ω₁ u) (fun w=> (U₀).bulk w e r))(h: Poly R.age_t fun i=> ‖biases (s i) e‖ₑ): Workday R.age_t (Ω₁ u) (χ e r):=by
 by_cases hv:r=2
 · subst r; apply plain_r; unfold chi; simp_rw [Warm.peak_at]; apply VacDay.sub (plain H); exact plain ((K_r S Y G Z Z₁).smul _ h)
 unfold chi;simp_rw [peak_dark _ hv,smul_zero,sub_zero];exact H
include T Tb T' Tb'
-- previous.e transition
lemma brew (he:0<e)(ht:e≤p)(h:r+1 ≤ e+2)(hx:1≤r)(H:∀ i<e,Carry β v fun p=>‖δ i p‖ₑ)(H':∀ i j,Earlier e (r+1) i j→ VacDay v β (Ω₁ u) (fun p=>(U₀).bulk p i j-(U₁).bulk (A.connects p) i j)):
 VacDay (v ∘ Flap.prev) α (fun i=>Ω₁ u i.next) (fun i=>Ω₃ e (r+1) i - valley S Y G Z s i (F e (r+1) i.prev)):=by
 obtain ⟨h₁,h₂⟩:=paid_r S Y G Z s S' s' A D D' R T Tb T' Tb' ht h hx
 have hb:= hopes_d S Y G Z s S' s' A D D' R h₁ h₂ (spark S Y G Z s S' s' A D D' R T Tb T' Tb' ht h hx H H')
 let q(f: Flap M):=offer (first_v S G f) (χ' e (r+1) (A.connects f.prev)); have hp: Workday α (N₂ u) q := epoch_P S Y G Z s (creep S G S' A R.measure R.width (coil_p S' Y G Z s' R.s (T' e ht _) (Tb' e ht)))
 have hh:= hopes_d S Y G Z s S' s' A D D' R hp hp (by simp_rw [sub_self]; exact zero_r)
 convert VacDay.add hb hh using 1;ext1 i; let X:= χ e (r+1) i.prev; let L:= χ' e (r+1) (A.fly i).prev
 unfold focusD bumpD; unfold q; rw [A.previous]; simp_rw [fun f:Flap M=>reprised (r:=r) S Y G Z s f he,fun f:Flap M'=> reprised (r:=r) S' Y G Z s' f he]; rw [inherits S Y G Z s i (sap_l S Y G Z s _) (sap_l S' Y G Z s' _)]; let U:= valley S Y G Z s i X; let T:= valley S Y G Z s i L; let V:=valley S' Y G Z s' (A.fly i) L
 change U+_-(V+_)-(U-T)= _ + (T - V); abel
end duel
end V
end YM.RegulatorIR.Venture

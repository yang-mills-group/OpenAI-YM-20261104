import YM.RegulatorIR.Venture.Gardens

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
private lemma deltaN (A B:Layer I I): petals (I:=X) A-petals B=petals (A-B):=by ext1 i;ext1 j; cases i <;> cases j <;> first| rfl|exact sub_zero _
private lemma deltaD (J K:Layer X I) : Function.swap (hoses J)-Function.swap (hoses K)= Function.swap (glued 0 (J-K) 0 0):=by ext1 i;ext1 j;cases i <;> cases j <;> first| rfl|exact sub_self _
section overlap
variable (H:∀ i:Page M,S'.l (A.connects i)=S.l i)(hp: Poly B.age_t fun i:Page M=>B'.age_t.val (A.connects i))
include H
lemma price_same (i: Page M): Ω₂ u (A.connects i)= Ω₁ u i :=by
 let p:= H i; unfold lnk; rw [self_tar (S'.l_p _), self_tar (S.l_p _)]
-- important different decks.Line counts. Tariffs normalized.
lemma price_aux (i:Flap M) : drifted S' G u (A.fly i)= drifted S G u i:=by
 have he:S'.l (A.fly i).prev=S.l i.prev:=by rw [← A.previous]; exact H _
 have hz:S'.l (A.fly i).next=S.l i.next:=by rw [← A.next];exact H _
 unfold drifted; congr 2
include hp
omit H in
lemma flightS : Poly α (fun i:Flap M=> B'.age_f.val (A.fly i)):=by
 have ht : Poly α (fun i=> B'.age_t.val (A.connects i.prev)):= hp.us Flap.prev
 convert ht using 1;ext1 i;rw [A.previous];rfl
lemma creep {T:Page M'→Packet (Foot G) e} (h:Workday B'.age_t (Ω₂ u) T) : Workday β (Ω₁ u) fun i=> T (A.connects i):=by obtain ⟨c,hc,h⟩:=h; exact ⟨_,renewed (hc.us A.connects) hp,fun i=>by rw [← price_same _ _ _ _ H];exact h _⟩
lemma draisin {T:Flap M'→Packet (KFoot G) e} (h:Workday B'.age_f (drifted S' G u) T): Workday α (drifted S G u) (fun i=>T (A.fly i)):=by obtain ⟨c,hc,h⟩:=h; exact ⟨_,renewed (hc.us A.fly) (flightS S S' A hp),fun i=>by rw [← price_aux _ _ _ _ H];exact h _⟩
lemma draisinL {T:Flap M'→Layer (KFoot G) (KFoot G)}(h:Beam B'.age_f (drifted S' G u) T): Beam α (drifted S G u) (fun i=> T (A.fly i)):=by obtain ⟨c,hc,h⟩:=h;exact ⟨_,renewed (hc.us A.fly) (flightS _ _ A hp), fun i=>by rw [← price_aux _ _ _ _ H];exact h _⟩
variable (W: Scripted S Y G Z p u B γ)(W': Scripted S' Y G Z p u B' γ)(hv: θ<γ)(ht:0≤θ)
include Z W W' hv ht
omit hv ht in
lemma beam_shapes : Beam α (drifted S G u) (fun i=> (A₀ i).line) ∧Beam α (drifted S G u) (fun i=> (A₁ (A.fly i)).line):= ⟨beam_l S Y G Z s W, draisinL _ _ _ A H hp (beam_l _ _ _ _ _ W')⟩ -- omit θ
omit H in
lemma rays_diff : RailDay (Reserve.peak_M B θ∘Flap.prev) α (drifted S G u) (fun i=> (A₀ i).line-(A₁ (A.fly i)).line):=by
 let D₁:= S.pulses Y G Z; let D₂:= S'.pulses Y G Z;let Y':= haloS S' u G Y
 obtain ⟨c,hc,h⟩:= pulse_rates Z A W.funding (renewed (W'.funding.currency.us A.connects) hp) W.bands (renewed (W'.bands.rays.us A.fly) (flightS _ _ _ hp)) hv ht
 refine ⟨_,hc, fun i=> ?_⟩
 let p:= drought Z A (F:=Y) i
 dsimp only; rw [show (A₀ i).line-(A₁ (A.fly i)).line=petals (I:=Foot G) p from deltaN _ _]
 have he(x y): p x y=p y x:=by change D₁ i x y-D₂ (A.fly i) x y= D₁ i y x - D₂ (A.fly i) y x; exact congr_arg₂ (·-·) (S.gifted Y G Z s i x y) (S'.gifted Y G Z s' (A.fly i) x y)
 have hz:= Oracle.row_wing (F:=Epoch.League.leftTr S G i) (L:=Epoch.League.rightTr S G i) (K:=Epoch.League.fares S u i) (Y:=Foot G) (A:=p) (h i|>.1) -- K param vs A
 refine ⟨hz,?_⟩; rw [petals, mirror_led, show Function.swap p=p from funext (fun x=>funext (fun y=>he y x))]; exact hz
omit H in
lemma slope_diff : RailDay (Reserve.peak_M B θ∘ Flap.prev) α (drifted S G u) (fun i=> (A₀ i).driftL-(A₁ (A.fly i)).driftL):=by
 obtain ⟨c,hc,h⟩:= settle_rates A W.funding (renewed (W'.funding.currency.us A.connects) hp) W.bands (renewed (W'.bands.down.us A.fly) (flightS _ _ _ hp)) hv ht Z; refine ⟨_,hc, fun i=>?_⟩; let p:= settle A Y G i; let d:=glued (0:Layer (Foot G) (Foot G)) p 0 0
 dsimp only; rw [show (A₀ i).driftL-(A₁ (A.fly i)).driftL= Function.swap d from deltaD _ _]
 obtain ⟨h₁,h₂⟩:=h i; have H:= h₁; change Layer.row p _ _ _ _ at H
 constructor
 · unfold d; rw [mirror_led]; convert halo_led (C:=Function.swap p) (A:=0) (B:=0) (D:=0) row_dark row_dark h₂ row_dark using 1 <;> first|rfl|simp
 change Layer.row d _ id id _;convert halo_led (A:=0) (B:=p) (C:=0) (D:=0) row_dark H row_dark row_dark using 1 <;>first|rfl|simp
omit H in
lemma cohort : VacDay (Reserve.peak_M B θ) β (lnk S G u) (fun i=>coil (S.scroll_j Y G i)-coil (S'.scroll_j Y G (A.connects i))):=by
 let f(i:Page M):= pipeline A G Y i
 have hp': Carry β (Reserve.peak_M B θ) (fun i=>amount (f i) u):= progressing Y A B G W.funding ht hv (renewed (W'.funding.currency.us A.connects) hp)
 have h: VacDay (Reserve.peak_M B θ) β (lnk S G u) f := by
    apply bonds_v _ hp';intro i
    let D:=S.scroll_j Y G i-S'.scroll_j Y G (A.connects i); change IsSym (Momentum.lamp D); have hx:Function.swap D=D:= crust_sym A _;let W:=coil_s D hx
    intro e z; apply mul_left_cancel₀ (show (-1/2:ℝ)≠0 from by norm_num); exact W e z
 convert h.tilts (-1/2:ℝ) using 1; ext1 i; ext1 j;exact (mul_sub ..).symm
end overlap
end V
end YM.RegulatorIR.Venture

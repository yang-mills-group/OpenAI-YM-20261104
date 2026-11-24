import YM.RegulatorIR.Warm.Kappa
import YM.RegulatorIR.Epoch.Palette

/-!
# Before calibrating clocks: at fixed Run and β every price finite and
ready as stated in linear equations. No warm estimates used here.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Stage
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {X:Type} {M:X→ℕ} {n:Page M→Side} (S:Circuit M n){K:KernelChoices}(Y:Program K) (G:Gauge)(Z:∀ P:Patch,P.Branches K G)(t:Page M→Scale)
local notation "A₁"=> S.dialect Y G Z t
local notation "Tr"=> S.lane Y G Z t
local notation "Q"=> S.payroll Y G Z t
local notation "P"=> Epoch.League.paceS
local notation "H"=> Epoch.League.haloS
variable (k:ℕ) (f:Flap M)
-- beam authority
lemma con (w:Page M): Layer.Sym ((A₁).maps w) ((A₁).maps w) ((Tr).stem w) ∧ Function.swap ((Tr).stem w)=(Tr).stem w ∧ Billed ((Tr).stem w):=by
 let U:=S.honored Y w; let V:=S.tables Y w
 let h:= U.card
 refine ⟨gears_A G (S.dual w) (S.comet w) (crustA G V) (tune_s G V h (fun n=>U.symmetryP n G)),symmetry_h G V h.floorP h.pos.le h.paid h.stripP.2.1,crust_f G V h.stripP.2.1 h.pos.le h.paid⟩
lemma physical (f:Flap M)(k): Layer.row ((A₁).frames f).line ((A₁).ceilingRoom.cone k f) id id (H S k G Y f) ∧ Layer.row (Function.swap (((A₁).frames f).line)) ((A₁).ceilingRoom.cone k f) id id (H S k G Y f):=by
 let i:= S.pulses Y G Z f
 obtain ⟨hp,hz⟩:=Epoch.League.hmA (S:=S) (F:=Y) Z f k; have Ht : Function.swap (((A₁).frames f).line)=petals i:=by rw [show ((A₁).frames f).line=petals i from rfl,petals,mirror_led,show Function.swap i=i from hp];rfl
 have hv: Layer.row i (Tariff.native _ (S.l_p f.next) k) (fm G (S.l f.prev)) (fm G (S.l f.prev)) (H S k G Y f):=hz
 rw [Ht]; exact ⟨row_wing (L:=fm G (S.l f.next)) hv,row_wing (L:=fm G (S.l f.next)) hv⟩
lemma chargeP (w:Flap M)(k) : Layer.row (S.sails Y G w) (Tariff.native _ (S.l_p w.next) k) (fm G (S.l w.prev)) (fm G (S.l w.next)) (P S k G Y w) ∧ Layer.row (Function.swap (S.sails Y G w)) (Tariff.native _ (S.l_p w.next) k) (fm G (S.l w.next)) (fm G (S.l w.prev)) (P S k G Y w):=by
 let U:= S.honored Y w.prev; exact tilts (S.pactP w) K G _ (S.predicted Y w).rows U.card.paid U.card.pos (q:=k) (S.l_p w.prev) (S.width_s w) (S.l_p w.next)
lemma clockpost (f:Flap M)(k): Layer.row ((A₁).frames f).driftL ((A₁).ceilingRoom.cone k f) id id ((P S k G Y f)+1) ∧ Layer.row (Function.swap (((A₁).frames f).driftL)) ((A₁).ceilingRoom.cone k f) id id ((P S k G Y f)+1) :=by
 obtain ⟨hL,h⟩:= chargeP S Y G f k;exact ⟨(row_core hL h).2,row_heals (F:=id) (K:=((A₁).ceilingRoom.cone k f)) (row_core hL h).1 (max_le le_self_add le_add_self) ⟩
lemma panes_p (f:Flap M)(k): P S k G Y f ≠⊤:= Oracle.post_f (S.pactP f) K G _
lemma arc_p (f:Flap M)(k) : H S k G Y f≠⊤:= Oracle.heat_fin (S.pactP f) K G _
lemma startupK (f:Flap M)(p r k:ℕ): localQ ((A₁).ceilingRoom.cone k f) ((S.devices Y G Z t f).addon p r) (valor (t f.prev) p*archive (S.pactP f) K G (Z _) p r k):=by
 have ht:=S.wheeled G Z t f; exact Circuit.pull_z G Z (P':=S.pactP f) (S.rail K f) rfl rfl (S.seats f) ht p r (S.l_p f.prev) (S.width_s f) (S.l_p f.next)
-- Σ fixed. Local Fourier.All.Pose.Lane.R moments

def Knows {X:Type}{p:ℕ}(Tq:Tariff X)(V:Packet X p):Prop:=∃ k:ℝ≥0∞, k≠⊤∧ localQ Tq V k
lemma flight_f (i:Page M)(k): (A₁).census.cone k i = path (S.l_p i) G.ColorIndex k:=rfl
lemma fuel_f (f:Flap M)(k): (A₁).ceilingRoom.cone k f=(Tariff.native _ (S.l_p f.next) k).uses (peak_o G (S.l f.prev) (S.l f.next)):= rfl
lemma learns_m (w:X)(p r k): Knows ((A₁).census.cone k (Page.opening M w)) ((Q).bulk (Page.opening M w) p r):=by
 let f:= Page.opening M w; let V:= t f
 have hx:= Circuit.serene G t w -- names
 have hp:= Oracle.Circuit.fitsV S G t w
 by_cases he:p=0
 · subst p; refine ⟨_,by exact ENNReal.zero_ne_top, ?_⟩; rw [show (Q).bulk f 0= _ from vacuum_lo (Circuit.padV G t w) hp]; exact local_zero _
 by_cases hr:r<2
 · refine ⟨0,ENNReal.zero_ne_top,?_⟩; rw [show (Q).bulk f _ _=_ from primary_low V hx (by omega) hr]; exact local_zero _
 by_cases hm:r ≤ p+2
 · let c:ℝ:=biases V (p+2-r)
   have h := primary_high V hx (show 0<p from by omega) (by omega) hm
   change Knows (path (S.l_p f) G.ColorIndex k) (many (Circuit.mural G t w) p r); rw [h]; exact ⟨_,ENNReal.mul_ne_top (a:=‖c‖ₑ) (by finiteness) (handle_fin G r r k), local_gold (handled G r r k (S.l_p f)) c⟩
 refine ⟨0,ENNReal.zero_ne_top, ?_⟩; rw [show (Q).bulk f p r=0 from Classical.not_not.mp (fun he=> hm (hp p r he).2)]; exact local_zero _
lemma to_bar (f:Flap M)(k)(i j) : ((A₁).bar.cone k f).road i j ≤ ((A₁).census.cone k f.prev).road i j:=by
 let l:=S.l f.prev; let s:=S.l f.next
 have hv : l≤s:= (A₁).climb f; change Tariff.amount s k (dist _ _)≤ Tariff.amount l k (dist _ _); unfold Tariff.amount;gcongr; exact S.l_p _; exact le_rfl
lemma enters {f:Flap M}{p:ℕ}{X:Packet (Foot G) p}{c:ℝ≥0∞}(h: localQ ((A₁).census.cone k f.prev) X c) : localQ ((A₁).bar.cone k f) X c:=by intro i x; apply le_trans _ (h i x); apply quota_mono; intro j; exact Tariff.diameter_le _ (Tariff.diameter_unit ..) (fun i k' =>(to_bar S Y G Z t f k _ _).trans (Tariff.diameter_ge _ j.val i k'))
def l₀ : Meter Unit := Aug.light.us (fun _=>1)
private lemma moving {I:Type}(L:Tariff I)(K:Layer I I){c:ℝ≥0∞}(hc:c≠⊤)(h:Layer.row K L id id c ∧ Layer.row (Function.swap K) L id id c): Beam l₀ (fun _=>L) (fun _=>K):=⟨_,Poly.standard _ hc,fun _=>h⟩
lemma traveling (w:Flap M)(k) (Pq:∀ e r,Knows ((A₁).census.cone k w.prev) ((Q).bulk w.prev e r)) : ∀ e r,Knows ((A₁).census.cone k w.next) ((Q).bulk w.next e r) :=by -- local notation conflict
 let R:=(A₁); let p:=Page.bindW w.prev; let v:= (Q); let A:=R.frames w; let F:=R.ceilingRoom.cone k w; let Y1:=v.bulk w.prev; let D:=A.jVac Y1
 have hp : ∀ e r, Knows F (D e r):=by
    intro e r
    obtain ⟨c,hc,h⟩:= Pq e r; have hr:= enters _ _ _ _ _ k h; let V:=R.ceiling w; let f:= firstChannel (R.maps w.prev) (R.maps w.next); let T':= (Step.combine (R.maps w.prev) (R.maps w.next)); have hF:localQ F (offer f.native (Y1 e r)) c:= local_offer _ (A:=Tariff.native (S.l w.next) (S.l_p w.next) k) hr -- fix
    let c' := valor (t w.prev) e*archive (S.pactP w) K G (Z _) e r k
    exact ⟨c+c', ENNReal.add_ne_top.mpr ⟨hc, ENNReal.mul_ne_top (valor_f _ _) (archived _ _ _ _ _ _ _)⟩, local_add hF (startupK _ _ _ _ _ _ _ _ _)⟩
 let T'(e:ℕ)(r):=ceaseHeat A.line D false e r
 have hs(j r): Workday l₀ (fun _=>F) fun _=>T' j r:=by
    unfold T' ceaseHeat heated;apply Workday.sum _ (Finset.range (3*j+1)); intro i _; apply Workday.hot (K:=fun _:Unit=> A.line) (V:=fun _ : Unit=>D) ?_ (moving F A.line (arc_p S Y G w k) (physical S Y G Z t w k)) false i j r (le_refl j)
    intro p hp' r; obtain ⟨c,hc,H₁⟩:= hp p r; exact ⟨_,Poly.standard _ hc,fun _=>H₁⟩
 intro e r;rw [← (Q).step_v w];unfold GridStep.pure; split
 next h0=> exact ⟨0,ENNReal.zero_ne_top,local_zero _⟩
 next _=>
    obtain ⟨c,hc,hH⟩:= (hs e r).draft_budget (K:=fun _=> A.driftL) (moving F A.driftL (ENNReal.add_ne_top.mpr ⟨panes_p S Y G w k,ENNReal.one_ne_top⟩) (clockpost S Y G Z t w k))
    let Tℓ:= Tariff.native _ (S.l_p w.next) k
    exact ⟨_,hc.cost (),local_crop (T:=draft A.driftL (T' e r)) (f:=(lastChannel (R.maps w.prev) (R.maps w.next)).native) (A:=Tℓ) (Step.combine (R.maps w.prev) (R.maps w.next)).pos (hH ())⟩
end YM.RegulatorIR.Stage

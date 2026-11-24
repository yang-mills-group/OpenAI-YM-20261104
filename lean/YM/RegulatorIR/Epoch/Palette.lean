import YM.RegulatorIR.Epoch.Gains

/-!
# W1 release includes differences on stochastic and deterministic rails
DO NOT expose $κ$ as β. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Epoch
open Function Set Filter Finset Lattice RG Wilson Gauge Budget Budget.Packet Budget.Tuple Budget.Layer Geometry Uniform YM.RegulatorIR.Ledger Step Taping Precision Laurent Bloch Oracle Quadratic ENNReal Exterior
open RegulatorIR.Momentum (trim path area)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X X' Y Y' I U :Type} {M:X→ℕ}{P:Page M→Side}{N:X'→ℕ}{Q:Page N→Side}{b u k p r:ℕ}
section tempo
lemma pays_life {A:Tariff X} {h:Y→X}{t:U→X}{z:I→X}{T:Layer Y U}{C:Layer U I}{c d:ℝ≥0∞} (H:Layer.row T A h t c)(ht:Layer.row C A t z d): Layer.row (lap T C) A h z (c*d):=by
 intro i;apply le_trans _ (mul_le_mul_left (H i) d); unfold quota; rw [← ENNReal.tsum_mul_right]
 let g(x:U)(y:I):= ‖T i x‖ₑ * A.road (h i) (t x) * (‖C x y‖ₑ * A.road (t x) (z y))
 calc
    _ ≤ ∑'y,∑'x,g x y := by
       apply ENNReal.tsum_le_tsum; intro y; refine (mul_le_mul_left (show ‖lap T C i y‖ₑ ≤ ∑' x, ‖T i x * C x y‖ₑ from enorm_tsum_le_tsum_enorm) _).trans ?_ -- test parameters
       rw [← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro x; rw [enorm_mul]; exact (mul_le_mul_right (A.tri (h i) (t x) (z y)) _).trans_eq (mul_mul_mul_comm ..)
    _ = ∑'x,∑'y,g x y:=ENNReal.tsum_comm
    _ ≤ _:= ENNReal.tsum_le_tsum (fun x=> by unfold g;rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right (ht x) _)
lemma row_neg_cost {A:Tariff X} {h:Y→X}{t:U→X}{T:Layer Y U}{c:ℝ≥0∞}(H:Layer.row T A h t c): Layer.row (-T) A h t c:=by intro i; rw [Pi.neg_apply,quota_neg]; exact H i
end tempo
namespace League
variable {S:Circuit M P}{T:Circuit N Q}{K:KernelChoices}{F:Program K}{G:Gauge}(Z:∀ W:Patch,W.Branches K G)
variable (A:Section S T) {B:Marked M}
local notation "Y"=> S.pulses F G Z
variable {γ θ:ℝ}
variable (C:Counselor G S p F B γ)
def haloS (S:Circuit M P)(p:ℕ)(G:Gauge)(F:Program K)(i:Flap M) := let j:=S.J i.prev; heatPost (S.pactP i) K G (F.receipt.Ω j) (F.receipt.α j) (F.receipt.η j) p
def paceS (S:Circuit M P)(p:ℕ)(G:Gauge)(F:Program K)(i:Flap M) := let j:=S.J i.prev; post_C (S.pactP i) K G (F.receipt.Ω j) (F.receipt.α j) p
-- `$Ω(width)` may be post-L, kept in this bill
-- cost.Scheduling.P of A & T both: overlaps need align even if eras independent.
structure Spectrum (S:Circuit M P)(p:ℕ)(F:Program K)(L:Meter (Flap M))(G:Gauge):Prop where
 rays : Uniform.Poly L (haloS S p G F)
 down : Uniform.Poly L (paceS S p G F)

-- transfer recurrence spine; no casting of lengths P needed for T universe. root transcript.
private lemma tapped {a b:Patch}{B:Bed}{s:Clip}{z q u:ℝ}(h:a=b)(H:Hall B z q u s): hearth a K G B H (Z a)= hearth b K G B H (Z b):=by subst a;rfl

private lemma pulses_co (i:Flap M): let w:= A.fly i; let H:=T.honored F w.prev;(T.pulses F G Z w)= hearth (S.pactP i) K G _ H.card (Z _):= tapped Z (A.pact i) _
private lemma hips_co (i:Flap M):let w:= A.fly i; let j:= T.J w.prev; ∃ H:Cross (S.pactP i).L (TypeFace 1) (TypeFace 1), BidP (S.pactP i) K (T.tables F w.prev) (T.tables F w.next) H (F.receipt.α j) (lesser (F.receipt.Ω j) (T.sizeL w)) ∧ T.sails F G w = projectionQ (S.pactP i) K H G:=by
 intro w j; rw [← A.pact]; exact ⟨T.tells F w,T.predicted F w, rfl⟩
lemma pulse_motion (i:Flap M) : Y i - T.pulses F G Z (A.fly i)= lap (Y i) (lap (- (S.scroll_j F G i.prev - T.scroll_j F G (A.connects i.prev))) (T.pulses F G Z (A.fly i))):=by
 rw [A.previous,pulses_co Z A, neg_sub]; exact heat_seed G (S.pactP i) ..
lemma wing_motion (i:Flap M) : S.sails F G i-T.sails F G (A.fly i)=lap (Y i) (lap (-(S.scroll_j F G i.prev-T.scroll_j F G (A.connects i.prev))) (T.sails F G (A.fly i))):=by
 obtain ⟨H,h,hp⟩:=hips_co (F:=F) (G:=G) A i;rw [hp,A.previous, neg_sub];
 exact diff_sail G (S.pactP i) (S.honored F i.prev).card _ (T.honored F _).card (S.honored F i.next).card (T.honored F _).card _ _ (S.predicted F i) h

def drought (i:Flap M) := Y i-T.pulses F G Z (A.fly i)
def settle (A : Section S T)(F:Program K)(G:Gauge)(i:Flap M): Layer (Prim.Foot G) (Prim.Foot G):= S.sails F G i-T.sails F G (A.fly i)
def leftTr (S:Circuit M P) (G:Gauge)(i:Flap M): Prim.Foot G→Room:= trim (S.l i.prev)
def rightTr (S:Circuit M P) (G:Gauge)(i:Flap M): Prim.Foot G→Room:= trim (S.l i.next)
def fares (S:Circuit M P)(p:ℕ)(i:Flap M):= Tariff.native (S.l i.next) (S.l_p i.next) p
def torso (S:Circuit M P)(p:ℕ)(G:Gauge)(i:Flap M):= (fares S p i).uses (leftTr S G i)
lemma crust_bill (i:Flap M) : Layer.row (S.scroll_j F G i.prev-T.scroll_j F G (A.connects i.prev)) (fares S p i) (leftTr S G i) (leftTr S G i) (amount (pipeline A G F i.prev) p*4^p):=by
 let D:= S.scroll_j F G i.prev-T.scroll_j F G (A.connects i.prev)
 have hp:S.l i.prev≤ S.l i.next:=by rw [S.width_s]; exact le_mul_of_one_le_right (S.l_p _|>.le) (by exact_mod_cast (S.sizeL i).property)
 have hz :Layer.row D ((RegulatorIR.Momentum.path (S.l_p _) G.ColorIndex p)) id id _:= lamp_row (S.l_p i.prev) D (u:=p)
 change Layer.row D (torso S p G i) id id _
 apply Layer.row_mono (B:=torso S p G i) (F:=D) (x:=id) (y:=id) (A:= RegulatorIR.Momentum.path (S.l_p _) G.ColorIndex p) _ hz
 intro i' j; change Tariff.amount (S.l i.next) p (dist _ _) ≤ Tariff.amount (S.l i.prev) p (dist _ _)
 unfold Tariff.amount; gcongr; exact S.l_p _; exact le_rfl

lemma hmA (i)(p): Function.swap (Y i)=(Y i) ∧ Layer.row (Y i) (torso S p G i) id id (haloS S p G F i):=by
 let h:= S.honored F i.prev;let V:=h.card
 exact ⟨t_warm (S.pactP i) K G _ V (Z _),reels (S.pactP i) K G _ (S.l_p i.prev) (S.width_s i) (S.l_p i.next) V (Z _) ⟩
lemma crust_sym (i: Page M): Function.swap (S.scroll_j F G i - T.scroll_j F G (A.connects i))= S.scroll_j F G i - T.scroll_j F G (A.connects i):=by
 let h:= S.honored F i; let v:= T.honored F (A.connects i); exact congr_arg₂ (·-·) (symmetry_h G _ h.card.floorP h.card.pos.le h.card.paid h.card.stripP.2.1) (symmetry_h G _ v.card.floorP v.card.pos.le v.card.paid v.card.stripP.2.1)
lemma hmB (i:Flap M)(p): let w:= A.fly i;let U:=T.pulses F G Z w; Function.swap U=U ∧ Layer.row U (torso S p G i) id id (haloS T p G F w):=by
 intro w u; let h:= T.honored F w.prev;let v:=h.card
 refine ⟨t_warm (T.pactP w) K G _ v (Z _),?_⟩
 change Layer.row (T.pulses F G Z (A.fly i)) _ _ _ _; rw [pulses_co Z A]; unfold haloS;dsimp only; rw [show T.pactP w=S.pactP i from A.pact _] -- points
 exact reels (S.pactP i) K G _ (S.l_p _) (S.width_s i) (S.l_p i.next) v (Z _)
lemma wBucket (i:Flap M)(p): Layer.row (T.sails F G (A.fly i)) (fares S p i) (leftTr S G i) (rightTr S G i) (paceS T p G F (A.fly i)) ∧ Layer.row (Function.swap (T.sails F G (A.fly i))) (fares S p i) (rightTr S G i) (leftTr S G i) (paceS T p G F (A.fly i)):=by
 obtain ⟨J,h,hp⟩:= hips_co A i (F:=F) (G:=G); rw [hp]; let w:= A.fly i; let V:= T.honored F w.prev; let f:= T.J w.prev; unfold paceS;dsimp only; rw [A.pact]
 rw [show T.sizeL (A.fly i)= (S.pactP i).L from congr_arg Patch.L (A.pact i)] at h 
 exact tilts (S.pactP i) K G J h.rows V.card.paid V.card.pos (S.l_p i.prev) (S.width_s i) (S.l_p i.next)
include C
lemma pulse_rates (H:Poly B.age_t (shareP G T p F∘A.connects))(S':Spectrum S p F B.age_f G)(T':Poly B.age_f (haloS T p G F ∘ A.fly))(he:θ<γ)(h:0≤θ) : RailDay (Reserve.peak_M B θ ∘ Flap.prev) B.age_f (torso S p G) (drought Z A (F:=F)) :=by
 let f(i:Page M):= amount (pipeline A G F i) p
 have ht:Carry B.age_t (Reserve.peak_M B θ) f:= progressing F A B G C h he H
 have hx : Carry B.age_f (Reserve.peak_M B θ∘ Flap.prev) (fun i:Flap M=> f i.prev*4^p):=(ht.us Flap.prev).mul_right (Poly.standard _ (show (4:ℝ≥0∞)^p≠⊤ by finiteness))
 refine ⟨_,Carry.mul_left S'.rays (Carry.mul_right hx T'),fun i=>?_⟩
 have hg: Layer.row (drought Z A (F:=F) i) (torso S p G i) id id (haloS S p G F i * (f i.prev*4^p*haloS T p G F (A.fly i))):=by
    rw [drought,pulse_motion Z A]; exact pays_life (hmA (S:=S) Z i p).2 (pays_life (A:=(torso S p G i)) (row_neg_cost (h:=id) (A:=torso S p G i) (crust_bill A i)) (hmB Z A i p).2)
 have hy : Function.swap (drought Z A (F:=F) i)=drought Z A i:= congr_arg₂ (·-·) (hmA (S:=S) Z i p).1 (hmB Z A i p).1
 exact ⟨hg,hy ▸ hg⟩ -- direction
lemma settle_rates (H:Poly B.age_t (shareP G T p F∘A.connects))(S':Spectrum S p F B.age_f G)(T':Poly B.age_f (paceS T p G F ∘ A.fly))(he:θ<γ)(h:0≤θ)(Z:∀ W:Patch,W.Branches K G) : ∃ f:Flap M→ℝ≥0∞, Carry B.age_f (Reserve.peak_M B θ ∘ Flap.prev) f ∧ ∀ i, Layer.row (settle A F G i) (fares S p i) (leftTr S G i) (rightTr S G i) (f i)∧ Layer.row (Function.swap (settle A F G i)) (fares S p i) (rightTr S G i) (leftTr S G i) (f i):=by
 let f(i:Page M):= amount (pipeline A G F i) p
 have ht:Carry B.age_t (Reserve.peak_M B θ) f:= progressing F A B G C h he H
 have hx : Carry B.age_f (Reserve.peak_M B θ ∘ Flap.prev) (fun i:Flap M=> f i.prev*4^p):=(ht.us Flap.prev).mul_right (Poly.standard _ (show (4:ℝ≥0∞)^p≠⊤ by finiteness))
 refine ⟨_,Carry.mul_left S'.rays (Carry.mul_right hx T'),fun i=>?_⟩
 let V:= S.scroll_j F G i.prev - T.scroll_j F G (A.connects i.prev)
 let y:= S.pulses F G Z i
 have hv:= hmA (S:=S) (F:=F) Z i p
 have he:= crust_bill (p:=p) (F:=F) (G:=G) A i
 obtain ⟨h₁,h₂⟩:= wBucket (F:=F) (G:=G) A i p
 rw [settle,wing_motion Z A];constructor
 · exact pays_life hv.2 (pays_life (row_neg_cost he) h₁)
 rw [lap_flip, lap_flip, hv.1, show Function.swap (-V) = -V from congr_arg Neg.neg (crust_sym (F:=F) (G:=G) A i.prev)]
 have hh:= pays_life (pays_life h₂ (row_neg_cost he)) (show Layer.row y (fares S p i) (leftTr S G i) (leftTr S G i) _ from hv.2)
 convert hh using 1; unfold f; rw [mul_comm _ (haloS ..)]; simp only [Function.comp_apply]; ring

end League
end YM.RegulatorIR.Epoch

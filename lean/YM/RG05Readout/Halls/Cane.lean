import YM.RG05Readout.Halls.Siren
/-!
# Cane -- cost to call Signatures without feedback loop

First estimate from captured pure transcript then cost on actual signed product
with enough in threshold units. Any stencil in geometry paid if coefficients
meet `tender`. Universal scalar receipts so sufficient UNIFORM aperture across
all correlation readings at regulated mesh, unselected or replicated. Inverse
compensation already paid back to RIGHT here. Only dimensional spatial gain
quoted, not yet physical test recovery or all perturbative costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Halls
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion Cells Overlay
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons Ribbons.ManyCopies OPE
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k g ℓ t v:ℕ}
set_option quotPrecheck false
local notation "Θ"=> C.path.levels
local notation "λ₀"=> C.path.levels.clock
local notation "Z!"=> C.path.levels.budget
local notation "S!"=> C.S
local notation "α"=> C.S.a
local notation "s!"=> C.S.scale
local notation "P!"=> C.side b p
variable (h:C.Makes){D: Address.Rail C} {ψ:ℕ→ℕ} {w:Worth} {B:ℕ→ℕ→ℝ}
    (Y:OPE.Package C w ψ D)(hC:Storage C D) (hS:Cater C D)
noncomputable def copperE (C:Family G) (m n d ℓ k v:ℕ) (q:ℝ):= Address.debit C n d (4*(1/ Many.fee C m (n+1) ℓ k v q)) -- namespace
abbrev tender (C:Family G) (m n d ℓ k v:ℕ)(Q:ℝ) := if h:n ≤ m then stringCost C h * (2*copperE C m n d ℓ k v Q+20*Shadow.bid C n d (copperE C m n d ℓ k v Q))+Q else Q
noncomputable def copperH (C:Family G) (m n d ℓ k v:ℕ)(Q:ℝ):ℝ:= let z:=tender C m n d ℓ k v Q; let w:=Many.fee C m (n+1) ℓ k v z; Shadow.safe C d n (copperE C m n d ℓ k v Q) w (4*(1/w))
section
variable {E:Type}{l:Filter E}{T:E→ℝ}{m n:E→ℕ}{Q r:E→ℝ}{B':ℝ}(hG:G.Simple)(ht:Tendsto T l atTop)(hm:Height C.S l T m 1)(hn:Height C.S l T n 1)(hN:∀ᶠ i in l, n i+1 < m i)(hQ:RateIs l T Q 0)(hR:∀ᶠ i in l, CaptureW C (n i+1) (m i) (r i) B')(hB:4 < B')
include hC Y hG ht hm hn hN hR hB
local notation "E1"=> fun i=> copperE C (m i) (n i) d ℓ k v
local notation "P1"=> fun i=> tender C (m i) (n i) d ℓ k v (Q i)
local notation "X1"=> fun i=> copperH C (m i) (n i) d ℓ k v (Q i)
omit hC Y hG hR hB in
lemma loops_term : RateIs l T (fun i=> if h:n i ≤ m i then stringCost C h else 1) 0:=by
    let Q'(i):= Real.exp (1*(s! (m i)-s! (n i))); have he':RateIs l T Q' 0:= ⟨Eventually.of_forall fun i=>Real.exp_pos _,by let Q:=hm.pace.sub hn.pace;rw [sub_self] at Q; exact Q.congr fun i=> by unfold Q'; rw [Real.log_exp,one_mul,sub_div]⟩
    exact RateIs.of_sandwich (RateIs.const ht (c:=1) one_pos) (he'.pays ht) (hN.mono fun i hi=>by rw [dif_pos (show n i ≤ m i by omega)]; exact Many.stampCosts _) (((hn.grows.eventually (string_paid (C:=C) zero_lt_one)).and hN).mono fun i ⟨hi,hk⟩=>by rw [dif_pos (show n i ≤ m i by omega)]; exact hi _ _) ht
include hQ
lemma paid_rates (hv:0<v) : RateIs l T (fun i=> E1 i (Q i)) 0 ∧ RateIs l T P1 0 ∧ RateIs l T X1 0:=by
    have h:Height C.S l T (fun i=>n i+1) 1:= hn.step (Θ).fits.mesh
    have hP:= scale_receipt hC hG ht hm h hN hR hB Y hQ ℓ k v hv; let Q1:=P1
    let f := fun i=> E1 i (Q i); have hF:RateIs l T f 0:= Shadow.debited hC hG ht hn (by apply RateIs.swap (((RateIs.const ht (c:=4) (by norm_num)).mul ((RateIs.const ht (c:=1) one_pos).div hP))); ring) d
    have hA:RateIs l T Q1 0:=by
       have hs:= (RateIs.const ht (c:=20) (by norm_num)).mul (Shadow.bidding hC hG ht hn hF d); have hX:= ((RateIs.const ht (c:=2) (by norm_num)).mul hF).add hs ht
       refine (((loops_term ht hm hn hN).mul hX).add hQ ht).swap (by norm_num) |>.congr ?_; filter_upwards [hN] with i hi; unfold Q1 tender; rw [dif_pos (show n i ≤ m i by omega),dif_pos (show n i ≤ m i by omega)]
    have he:=scale_receipt hC hG ht hm h hN hR hB Y hA ℓ k v hv
    refine ⟨hF,hA,Shadow.safely hC hG ht hn (by apply RateIs.swap (((RateIs.const ht (c:=4) (by norm_num)).mul ((RateIs.const ht (c:=1) one_pos).div he))); ring) hF he d⟩
omit hC Y hG hm hn hN hR hB hQ -- maybe
end
section root
variable (s:V→ℕ)(u: V→ Cover)(F:V→Body){r Q a:ℝ}(H: Knock b n m p k d ℓ t r a C s u F)(x:(i:V)→Palette C (s i))(A:(i:V)→Sight C (s i) p)(U:(i:V)→Emblems C (s i))(P:Sight C d p)(S:Emblems C d)
    (W:PulseC)(hW:Priced d W 1)(hp:∀ i:V, size (x i)≤ Q)(hQ:0 < Q)(h'A :∀ i:V,Spine D B h (n+1) p (s i) N (A i) (U i))(hU:Spine D B h b p d N P S)(hw:Awake D B b d)(hg:d+3 ≤ C.path.levels.clock.J n)(hN:m≤N)
local notation "V'"=> Fintype.card (Color V)
local notation "e!"=> copperE C m n d ℓ k (Fintype.card (Color V)) Q
local notation "u!"=> fee C m (n+1) ℓ k (Fintype.card (Color V))
local notation "q0"=> tender C m n d ℓ k (Fintype.card (Color V)) Q
local notation "Q!"=> copperH C m n d ℓ k (Fintype.card (Color V)) Q
local notation "o"=> (fun j:V=>Lattice.wrap (C.side (n+1) p) (u j))
local notation "h!"=> H.east.le.trans hN
local notation "he"=> (H.level.trans n.le_succ).trans h!
local notation "X"=> bunchG (C:=C) (N:=N) o s F (fun j=> Many.point (U j) (x j) m N)
local notation "X'"=> amplitude C n N p d W (dyes C (n+1) N p h! X)
variable {R:ℕ→ Palette C d} {T:∀ i:ℕ,Tape G (C.side i p)}
local notation "M"=> finer S (n.le_succ.trans H.east.le) (R n- Shadow.advances S R b n)
local notation "x!"=> Records.rebirth C d n p N h! W (Many.point S M m N) X
include H h Y hC hS h'A hU hp hN hQ hg hw hW
set_option maxHeartbeats 660000 in
lemma onAll (hX:Signature C p b n N d h D P X' e! R T) (hPin: ∀ i,b≤ i→Pin C i d) (j:ℕ)(ht:j ≤ b)(A':Stock.Tabs.opens C.path.levels (bumper (2*t)) j b): size (M) ≤ q0 ∧ ∀ (z:Site (C.side b p)),separation z 0 ≤ (C.S.toDepth ht p).count.val/4 → ∀ (q:Body),Cap (d+2) q 1 →
    0< Q!∧ (Cells.center C.S p (ht.trans he) 0).rootTest (C.beta N p) (uniform C (n+1) p N d h! x! b z (1,false) q) ≤ Real.exp (baseT C j b d)/ (focus C Q! n b):=by
    let q' := q0; have hm : n ≤ m:= n.le_succ.trans H.east.le; have hp1: size (M) ≤ stringCost C hm * (2*e! + 20* Shadow.bid C n d e!):= Shadow.codifies h hU H.level hN hm (hPin _ (le_refl b)).lit.1 hX -- parameters? ok
    have hv:size M+ Q≤ q' := by unfold q' tender; rw [dif_pos hm]; exact add_le_add_left hp1 Q
    have hx: Q ≤ q':= (le_add_of_nonneg_left (size_ge _)).trans hv; have hZ : size M ≤ q':=(le_add_of_nonneg_right hQ.le).trans hv
    exact ⟨hZ,fun z he₃ q hc=> realNorm h Y hC hS s u F H x A U P S W hW q' (fun i=>(hp i).trans hx) (hQ.trans_le hx) h'A hU hw hg hN hPin hX hZ ht A' z he₃ q hc⟩
end root
end YM.RG05Readout.Halls

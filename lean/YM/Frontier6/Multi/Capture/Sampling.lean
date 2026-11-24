import YM.Frontier6.Multi.Capture.Layout

/-! Scene threading across cell seams via root anchors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies.Doors
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Matrix
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank Next.Rank.Station Cells
open Ribbons
open scoped Topology BigOperators Classical
variable {G:Gauge}{O:Type}[DecidableEq O][Fintype O]
variable (C:Family G)(J j p:ℕ)
variable (L : O → Site (C.side j p))
set_option quotPrecheck false
local notation "Q"=> hands C p J
local notation "V"=> Site (C.side J p)
local notation "E"=> Mix.camp C p J

local notation "Y"=> placements C J j p L
variable {δ φ ψ ζ:ℕ→ℝ}{u:ℕ→ℕ→ℝ} {W:Bid.Worth}{r:ℕ→ℕ}{D:∀ N p i,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (h:Scrim C W ζ ψ φ δ u r D) {χ:ℕ→ℝ}{d:ℕ}{ε:ℝ}
variable (h' : WaresAll C (δ:=δ) (r:=r) (μ:=D) (C.ref d) d χ δ (PhysicalNext.Repeat.Legato.bling C.path.levels)) {N m k i:ℕ}
variable (w:O→ℝ) (F:O→ Config G (C.side N p)→ℂ)(hi:∀ i,Continuous (F i))
local notation "T"=> center C.S p
local notation "Z"=> Now (Site (C.side J p)) O

def allCopy (hN:J≤N) (x:Live (Site (C.side J p)) O): Config G (C.side N p)→ℂ:= (center C.S p hN 0).copy x.1 (F x.2)
local notation "f'"=> allCopy C J p F
-- Lean param order inspect
lemma totalCopy (hN:J≤N)(x: Site (C.side J p)): ∀ U:Config G (C.side N p), (center C.S p hN 0).copy x (∏ i,F i) U=∏ i,f' hN (x,i) U:=by
    intro U; unfold Tiling.copy allCopy; simp_rw [Tiling.copy];split_ifs <;> simp [star_prod]
local notation "P'"=> C.path.levels.budget
local notation "R"=> C.path.rep N p
local notation "X"=> PhysicalNext.Repeat.Legato.bling C.path.levels m
variable (hM:C.Makes)(hR:Created C)(root:O)
local notation "T'"=> Equiv.swap (0 : V)
local notation "Φ"=> C.path
local notation "τ"=> fun hN:J ≤ N=> birth Z (C.path.rep N p N) (f' hN)

include h h' hM
lemma prepared (hm:J ≤ m)(hj:m+1<j) (hN:j<N) (t:O→ℕ)(q:(i:O)→ C.label (t i))(B:O→ℝ)
    {σ:ℕ→ℝ}(hT:Canopies.Thor C.path δ r D σ χ (C.ref d))(hG:Travel C.path δ r D χ 0 (Q) T' E (placements C J j p L) m j (C.ref d) ε N)(hF:Integrable (τ (hm.trans (m.le_succ.trans (hj.le.trans hN.le)))) (prior G _)) (hv:Daylight (0:Site (C.side J p)) (placements C J j p L j) (C.path.levels.budget j).B)
    (hB:∀ i,0<B i)
    (ht:∀ i,C.ref (t i)≤j)(hp:∀ i,B i*Next.Rank.Spindle.paid C (t i) j N p (q i)≤ u (t i) j)
    (he:∀ i:O,F i= C.O N p (q i) (placements C J j p L N (0,i)))(hw:∀ i, w i=δ j*(φ j* B i)/8): Storage C.path 0 Q T' E (placements C J j p L) root (τ (hm.trans (m.le_succ.trans (hj.le.trans hN.le)))) j j hN.le ε (total w) :=by
    let hJN:= hm.trans (m.le_succ.trans (hj.le.trans hN.le))
    have hL: m<j:= lt_trans m.lt_succ_self hj; have hv':C.ref d < j:=lt_of_le_of_lt hG.advance hL
    have hb(i) : f' hJN (0,i)=F i:= by unfold allCopy; exact funext (Tiling.copy_zero _ _)
    have hU : Migrating Φ j p N E:= uphill C J j p N (hm.trans hL.le)
    obtain ⟨l,g,L',hS,hχ,hC⟩:= Canopies.upper C t N j p W ζ ψ φ δ u r D q (placements C J j p L) (fun _=> (1,false)) B 0 E Q T' (f' hJN) σ χ h.costs hM hT hv'.le ht hN ((hG.clear j hL le_rfl).sectors _ _ (r j) (hG.ceiling j hL.le) (P' j|>.B_pos)) (transit C J j p L (hm.trans hL.le) N) (hv.drake _ _ _ (hG.shaped j hL le_rfl) (hG.clear j hL le_rfl)) hp ‹_› hU hG.exchange (fun i he hn x hc y=> shaped _ _ _ _ _ ((hm.trans hL.le).trans he) x hc y) (fun i h b=> by rw [hb]; exact (handmove C N p J hJN ..).symm) (fun i=> by rw [hb,he]; exact (itemT C N p _ hM _ _).symm) hF
    have hA:= h'.funs j hv'.le
    refine inaugural Φ δ r D σ χ 0 Q T' E (placements C J j p L) hM.wilson (C.ref d) hT _ root ε w hN hv' ?_ (h'.crisp j hv'.le) ?_
    · rw [show (fun i=>8*w i)=(fun i=>δ j*(φ j* B i)) from (funext (fun i=>by rw [hw]; ring))]; exact ⟨g,L',l,hC,hS,hχ⟩
    · intro i; rw [hw]; exact div_pos (mul_pos hA.1 (mul_pos (h.costs.stay.water j (Nat.zero_le _) |>.1) (‹∀ i,0<B i› _))) (by norm_num)
end YM.MergeProof.Canopies.Doors

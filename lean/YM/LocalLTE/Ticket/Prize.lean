import YM.LocalLTE.Ticket.Pot
/-!
## Slip transactions for the cost estimator

Cylinders may be accessed by these *same* ports.
Personal program used on incoming
models, body validity for another actual magnitude cannot substitute for the receipts
on that model. Norm uses all links in site sets. Energy bills overbook
some binomial/readout prices; K includes none of the PDF normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Ticket
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{k d:ℕ}{F:Labels.Frame G d} (D:SectionData F) (A:Hol G)
local notation "O" => H.rep N p m
local notation "P" => H.rep N p (m+1)
local notation "V₀"=> H.S.side (m+1) p
local notation "V"=> H.S.side m p
local notation "κ" => Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "κ'" => Real.sqrt (H.levels.clock.forcedAllowance (m+1))
-- model book.RQ acceptable for ALL desks incl output capacities not enough for a paid model.As long after.L scheduled sender.
open Extra.Histories.InputColumn
variable (Q: Gateway F A (H.rep N p (m+1)) (H.S.side m p) ) (Q': Pigment A F (H.rep N p (m+1)) (H.S.side m p))
set_option quotPrecheck false
variable {B:F.Coeff→ Coefficient F (H.S.side (m+1) p)}
variable {k e uL τ:ℝ}{a θ ℓ b U u:ℕ}
variable (W:Voice F H p (m+1))(S:Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)(T:Employ H N p A m W S)
local notation "V1" i=> W.index.symm (Size.axis F i)
local notation "ass" i=> T.fullP i
variable (Y:∀ i,Inlet (H:=H) (N:=N) (p:=p) (m:=m) D A k a U (B (W.index.symm (Size.axis F i))) τ)
variable (i : F.Index)
-- probe preserve P.B orientation. Uses Gain only as preview. True.syllable suppressed, layouts on P from true only where all mode ZERO.Term costs. Reads at phase output no assertion at limit.
local notation "Hd"=> R.currents i
set_option quotPrecheck false
variable {C:Tariff}(h:Dues D A (H.rep N p (m+1)) (H.rep N p m) Q Q' (Real.sqrt (H.levels.clock.forcedAllowance m)) k a b U u C)(hp:F.coeffSize ((Vinca.unitP F H p m).x) ≤ C.issue)
local notation "x0"=> (H.levels.params (m+1)).columns
local notation "cv"=> C.first x0 τ e
local notation "ce"=> C.second x0 τ e (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))
variable (hs:Funds (m:=m+1) k A a U D (H.rep N p (m+1)) W B (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) e τ) (hz: Heard D H N p A (m+1) W)
open Motion
-- ZERO and alias tags. Padded layouts remain after rotating. Never compute ΠL from an answer.Support footprint binding for every row, even blanks; uses W charge only in authorization.Evaluate in input coordinates W.index kept. Normalize probes at present reader.Energy stencil occupations disclosed.For going further on *calibrated* phases, need additional policies.
local notation "yμ"=> Tally F
noncomputable def galleryC := pencil (code (Tally F)) (fun j:Tally F=> audition (T.turns j.1) (balls D A Q Q' W S T Y j.2)) ((chips F).comp W.index.toLinearMap)
local notation "p0"=> rotationP F (H.rep N p m).p.order (H.rep N p m).p.power
variable (V': Voice F H p m)(hX: V'.plays=Vinca.marksP H N p A m W S Q T)
    (ht:D.Sound A)
local notation "p₁"=> orbitCost F
local notation "Vw" v=> F.coeffSize (W.index v)
local notation "Vk"=> Vinca.marksP H N p A m W S Q T
variable {μ:ℝ}(hr:ConnectedActivityE6.Reliable G k μ)
include hr ht hX h hp hs hz
lemma portrait (v:F.Coeff) : let z:=galleryC D A Q Q' W S T Y v
    Exhibition D k u b A (H.rep N p m) (V'.plays v) z (Real.sqrt (H.levels.clock.forcedAllowance m)) ((p0*cv)*p₁* (Vw v)) ((p0*ce)*p₁* (Vw v)):=by
    intro z
    have he i:= gates D A Q Q' W S T Y i h hp hs hz
    let p':= p0; have hk: 1 ≤ p':= River.rotation_one ..
    let a:= W.index v
    let g(j:Tally F):= Planned.GuardedAtom.audition (T.turns j.1) (balls D A Q Q' W S T Y j.2)
    let g0(j:Tally F):= audition (T.turns j.1) (Vinca.parcelP H N p A m W S Q T j.2)
    let X'(j:Tally F):= Extra.Histories.stretch (chips F a j) (g j)
    let P'(j:Tally F):= Extra.Histories.stretch (chips F a j) (g0 j)
    let e' := ce; let v':= cv
    have hf(j:Tally F) := River.pitch j.1 (T.turns j.1) (he j.2) ht hr ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p))
    have hs'(j) := (hf (j:Tally F)).buckets (chips F a j)
    rw [hX]
    refine (River.auctions (k:=k) _ P' X' hs' Summable.of_finite Summable.of_finite (Real.sqrt_pos.mpr (forcedPos ..))).pledge ?_ ?_
    · rw [tsum_fintype,← Finset.sum_mul]; let i:=(0:F.Index); let u:= p'* v'; have ht':0≤u:= mul_nonneg (zero_le_one.trans hk) (he i).stock.cost; exact (mul_le_mul_of_nonneg_right (MergeProof.rip F a) ht').trans_eq (by unfold u p' v' a; ring)
    rw [tsum_fintype,← Finset.sum_mul]; let i:= (0:F.Index); let u':=p'*e'; have ht':0 ≤ u':= mul_nonneg (zero_le_one.trans hk) (he i).fee.first; exact (mul_le_mul_of_nonneg_right (MergeProof.rip F a) ht').trans_eq (by unfold u' p' e' a; ring)
variable {M:Worth}(hW: roomCost H.levels M)(hβ:Bank M H.levels)(ht':Responds D H N p M m W V')(he: Heard D H N p A m V')
include hW hβ ht' he
lemma press : let p0':=p0; let v0:=(p0'*cv)*p₁; let eZ:=(p0'*ce)*p₁; Funds (m:=m) k A b u D (H.rep N p m) V' (galleryC D A Q Q' W S T Y) κ (eZ*x0) (v0*x0):=by
    intro p0' uC eC v t
    let i:F.Index:=0; have hi := gates D A Q Q' W S T Y i h hp hs hz
    have hP :0≤ p0':= zero_le_one.trans (River.rotation_one ..); let P':=p₁; have hG :0≤P':=zero_le_one.trans (orbitCost_one_le _)
    apply (portrait D A Q Q' W S T Y h hp hs hz V' hX ht hr v).pledge
    · have hb : F.coeffSize (W.index v) ≤ x0 *t:=by
         have hb := Work.G08.cone_step M H hW hβ m F _ _ _ _ (ht'.tally v) (by rw [hz.currents]; exact hz.cone v)|>.2.1
         rw [hz.currents,he.currents] at hb; exact hb
      rw [mul_assoc uC]; exact mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hP hi.stock.cost) hG)
    have hb := Work.G08.cone_step M H hW hβ m F _ _ _ _ (ht'.tally v) (by rw [hz.currents]; exact hz.cone v)|>.2.1
    rw [hz.currents,he.currents] at hb
    rw [mul_assoc eC]; exact mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hP hi.fee.first) hG)
end YM.LocalLTE.Ticket

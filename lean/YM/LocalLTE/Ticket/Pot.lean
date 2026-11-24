import YM.LocalLTE.Ticket.Pip
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
abbrev Funds (k:ℝ)(A:Hol G)(a U:ℕ) (D:SectionData F)(R:Rep G (H.S.side m p))(UQ:Voice F H p m)(B:F.Coeff→ Coefficient F (H.S.side m p))(η e v:ℝ):Prop := ∀ f:F.Coeff, let p:= F.coeffSize (UQ.index f); Exhibition D k U a A R (UQ.plays f) (B f) η (v*p) (e*p)
-- notation `κ` clashes
variable (W:Voice F H p (m+1))(S:Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)(T:Employ H N p A m W S)
local notation "V1" i=> W.index.symm (Size.axis F i)
local notation "ass" i=> T.fullP i
variable (Y:∀ i,Inlet (H:=H) (N:=N) (p:=p) (m:=m) D A k a U (B (W.index.symm (Size.axis F i))) τ)
variable (i : F.Index)
-- probe preserve P.B orientation. Uses Gain only as preview. True.syllable suppressed, layouts on P from true only where all mode ZERO.Term costs. Reads at phase output no assertion at limit.
noncomputable def balls := Ticket.issueC D A Q Q' (MergeProof.rack S (W.plays (V1 i))) (T.fullP i) (Y i) i
local notation "Hd"=> R.currents i
set_option quotPrecheck false
variable {C:Tariff}(h:Dues D A (H.rep N p (m+1)) (H.rep N p m) Q Q' (Real.sqrt (H.levels.clock.forcedAllowance m)) k a b U u C)(hp:F.coeffSize ((Vinca.unitP F H p m).x) ≤ C.issue)
local notation "x0"=> (H.levels.params (m+1)).columns
local notation "cv"=> C.first x0 τ e
local notation "ce"=> C.second x0 τ e (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))
variable (hs:Funds (m:=m+1) k A a U D (H.rep N p (m+1)) W B (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) e τ) (hz: Heard D H N p A (m+1) W)
include hs in
lemma opportunities : Nonempty (∀ i,Inlet (H:=H) (N:=N) (p:=p) (m:=m) D A k a U (B (W.index.symm (Size.axis F i))) τ):=by
    have h (i:F.Index):= hs (V1 i)
    have hx i: F.coeffSize (W.index ((V1 i)))=1:=by rw [LinearEquiv.apply_symm_apply,Size.size_axis]
    refine ⟨fun i=> ?_⟩; let v:= V1 i; have he:=h i; have hy:τ * F.coeffSize (W.index v)=τ:=by unfold v; rw [hx,mul_one]
    obtain hx:= he.stock; rw [hy] at hx; exact ⟨he.format,hx.regular.choose, hx.regular.choose_spec.1,hx.regular.choose_spec.2⟩
include h hp hs hz
lemma gates : Exhibition D k u b A (O) (Vinca.parcelP H N p A m W S Q T i) (balls D A Q Q' W S T Y i) κ cv ce:=by
    let v:= V1 i; let f:=W.plays v; let f':=B v; let Pκ:=MergeProof.rack S f; let t:= W.charge v
    let T':=T.fullP i; have he0:=hs v
    have hL: F.coeffSize (W.index v)=1:=by unfold v; rw [LinearEquiv.apply_symm_apply,Size.size_axis]
    have he:=show Exhibition D k U a A (H.rep N p (m+1)) f f' (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) τ e from ?_
    · have hr:t ≤ x0:=calc _ ≤ _:= hz.cone v
                           _ ≤ (H.levels.params (m+1)).columns*F.coeffSize (W.index v):= mul_le_mul_of_nonneg_left (Work.G08.size_core F _) (zero_le_one.trans (H.levels.params (m+1)).columns_ge)
                           _ = _:=by rw [hL,mul_one]
      have hP:= T'.front
      have hk := Extra.Histories.forcedPos H.levels (m+1); have hκ:0≤T'.k:= nonneg_of_mul_nonneg_right (sumBudget_credit T'.pier) (Real.sqrt_pos.mpr hk) -- lemma name.
      have hU:=he.fee.regular
      have hK:= he.fee.forced
      have hh : (Vinca.decrement f f').forced=f.forced:= by change f.forced-f'.forced=_; rw [he.stock.forced,sub_zero]
      have ht: (MergeProof.rack S (Vinca.decrement f f')).forced=Pκ.forced:=by unfold Pκ MergeProof.rack MergeProof.stowK; rw [hh]
      apply Ticket.balances D A Q Q' Pκ T' (Y i) i h hp x0 ⟨hP.1,hP.2.1,hP.2.2.trans ((le_add_of_nonneg_right hκ).trans (T'.uniont.trans hr))⟩ he.layout hU
      obtain ⟨s,r',hv,_,hx,_,H₁,q,hq,hQ⟩:= MergeProof.keeps S _ (he.fee.bound le_rfl)
      rw [← ht]; exact ⟨q,⟨hq.1,hq.2.1, hq.2.2.trans (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hv).trans hx) (Real.sqrt_nonneg _))⟩,hQ⟩
    simpa [hL] using! (show Exhibition _ _ _ _ _ _ _ _ _ (τ*F.coeffSize (W.index v)) (e * F.coeffSize (W.index v)) from hs v)
end YM.LocalLTE.Ticket

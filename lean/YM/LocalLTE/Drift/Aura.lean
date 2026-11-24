import YM.LocalLTE.Drift.Hutch
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
namespace YM.LocalLTE.Drift
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
open Drift
local notation "R'"=> H.rep N p (m+1)
local notation "Gp"=> Config G (H.S.side (m+1) p)
-- Catalog from Bank. import uses integer horizon K. Real rows only incl witness layouts.
variable {K S:ℕ}{k:ℕ→ℕ}{F₁:ℕ→ Coefficient F (H.S.side (m+1) p)}
set_option quotPrecheck false
variable {l γ:ℝ} {s s' e: ℕ→ℝ}
variable (U:Gateway F A (H.rep N p (m+1)) (H.S.side m p)) (T:Drift.Etching D A (H.rep N p (m+1)) (H.S.side m p) k K S l)
variable (w:ℕ){A0:ℝ}(t:ℕ→ℕ→ℝ) -- t.Error costs per predictor query
variable (C:TariffX)(hx:Works D A (H.rep N p (m+1)) (H.rep N p m) w U T (Real.sqrt (H.levels.clock.forcedAllowance m)) C)(hp:F.coeffSize (Vinca.unitP F H p m|>.x) ≤ C.token.issue)

variable {Y:F.Coeff→ ℕ→ Coefficient F (H.S.side (m+1) p)}
variable (W:Voice F H p (m+1))(X:Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)(P':Employ H N p A m W X) (i:F.Index)
local notation "vV"=> H.rep N p (m+1)
local notation "y"=> W.index.symm (Size.axis F i)
local notation "u₀"=> (H.levels.params (m+1)).columns
local notation "a"=> W.plays y
local notation "c"=> W.charge y
local notation "T0" j=> Vinca.parcelP H N p A m W X U P' j
variable (Y':Paper (H:=H) (m:=m) (N:=N) (p:=p) D A (Y (W.index.symm (Size.axis F i))) K k S l s s')
noncomputable def colors (j:ℕ)(hj:j≤K):=Drift.auction D A (MergeProof.rack X (W.plays (W.index.symm (Size.axis F i)))) U T (P'.fullP i) Y' i j hj
local notation "f0"=> (Drift.colors D A U T W X P' i Y') -- order
variable (hk:∀ j,j≤K→ Exhibition D l S (k j) A (H.rep N p (m+1)) (W.plays (W.index.symm (Size.axis F i))) (Y (W.index.symm (Size.axis F i)) j) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) (s j) (e j)) (hy:Heard D H N p A (m+1) W)
open Motion
include hp hx hk hy
local notation "ν"=> (fun i:ℕ=> (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))*(e i+e i))
set_option maxHeartbeats 300000 in
lemma rainbowU : (∀ (j:ℕ) (hj:j≤K), Exhibition D l w (k j) A (H.rep N p m) (T0 i) (f0 j hj) (Real.sqrt (H.levels.clock.forcedAllowance m)) (C.peak ((H.levels.params (m+1)).columns) s s' e j) (C.delta ((H.levels.params (m+1)).columns) s s' e ν j))∧
       ∀ (j:ℕ) (hj:j<K), k j ≤ k (j+1)→ Patrons D l w (k (j+1)) ((H.rep N p m).p) (Vinca.decrement (f0 (j+1) hj) (f0 j hj.le)) (C.slip ((H.levels.params (m+1)).columns) s s' e (j+1)+C.slip ((H.levels.params (m+1)).columns) s s' e j):=by
    let aX:= y; let f Yy:= Y aX Yy; let Q0:= a; let Sτ:= X; let u:= MergeProof.rack X Q0; let T':=P'.fullP i; let P₂:= T0 i
    have he1:F.coeffSize (W.index aX)=1:=by unfold aX; rw [LinearEquiv.apply_symm_apply,Size.size_axis]
    have he: W.charge aX ≤ u₀ := by
        have he : _ ≤ ((H.levels.params (m+1)).columns)*F.coeffSize (W.index aX):= (hy.cone aX).trans (mul_le_mul_of_nonneg_left (Work.G08.size_core F _) (zero_le_one.trans (H.levels.params (m+1)).columns_ge))
        rwa [he1,mul_one] at he
    have hκ' :0 < κ':= Real.sqrt_pos.mpr (Extra.Histories.forcedPos H.levels _)
    have hQ:SumBudget (fun i=>(H.rep N p (m+1)|>.p.mass (u.support i) (T'.a i))) u₀:=by refine ⟨T'.front.1,T'.front.2.1,T'.front.2.2.trans ?_⟩; have h0:0≤T'.k:= nonneg_of_mul_nonneg_right (sumBudget_credit T'.pier) hκ'; exact (le_add_of_nonneg_right h0).trans (T'.uniont.trans he)
    have hA(j:ℕ)(hp:j≤K): u.regular=Q0.regular ∧ u.support= (f j).support:= ⟨rfl,hk j hp |>.layout⟩ -- actual rep only rack.I.Valid
    let L j:= f j; have hF (j:ℕ)(hp:j≤K) : ∃ t:ℕ→ℝ, SumBudget (fun i=>(H.rep N p (m+1)|>.p.mass (u.support i) (t i))) (e j)∧ ∀ i,(H.rep N p (m+1)).p.supBounds 0 (u.support i) (u.regular i-(f j).regular i) (t i):= by obtain ⟨b,hb,h0⟩:=(hk j hp|>.fee.regular); exact ⟨b,hb,fun i=>h0 i⟩
    choose t ht hT using hF; let b i q:= if h:i≤K then t i h q else 0
    have ht'(i)(h:i≤K):b i=t i h:=funext fun _=>dif_pos h
    have hZ(i)(hi:i ≤ K): SumBudget (fun j=>(H.rep N p (m+1)|>.p.mass (u.support j) (b i j))) (e i):=by rw [ht' _ hi];exact ht i hi
    have hX(i:ℕ)(ht:i ≤ K)(j): (H.rep N p (m+1)).p.supBounds 0 (u.support j) (u.regular j-(f i).regular j) (b i j):=by rw [ht' _ ht]; exact hT i ht j
    let Rb i:=κ'*(e i+e i); have hs j (hj:j≤K): Local.ForceCost (H.rep N p (m+1)).p (H.rep N p (m+1)).activities u.forced (Rb j):=by
        have hv := hk j hj; let d:=decrement Q0 (f j); have ht:d.forced=Q0.forced:=by change _- (Y _ _).forced=_; rw [hv.stock.forced,sub_zero]
        have hg:(rack X d).forced=u.forced:=by unfold u MergeProof.rack MergeProof.stowK; rw [ht]
        obtain ⟨s₂,r',hh,_,hm',_,hk',q,hq,hv'⟩:=MergeProof.keeps X _ (hv.fee.bound le_rfl); rw [← hg]; exact ⟨q,⟨hq.1,hq.2.1,hq.2.2.trans (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hh).trans hm') hκ'.le)⟩,hv'⟩ -- cast
    constructor
    · intro j hj; obtain ⟨q,hq,hp'⟩:= hs j hj; exact Drift.ballet D A u U T T' Y' i w b C hx hp (hA _ (Nat.zero_le _)|>.2) hX j hj hQ hZ q Rb hq hp' -- order
    intro j hj h; obtain ⟨q,hq,hp'⟩:= hs j hj.le; exact Drift.bridgeP D A u U T T' Y' i w b C hx hp (hA _ (Nat.zero_le _)|>.2) hX j hQ hZ q hp' q hp' hj h
end YM.LocalLTE.Drift

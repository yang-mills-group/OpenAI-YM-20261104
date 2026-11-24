import YM.LocalLTE.Drift.Work
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
variable (R:Coefficient F (H.S.side (m+1) p))
variable (U:Gateway F A (H.rep N p (m+1)) (H.S.side m p)) (T:Drift.Etching D A (H.rep N p (m+1)) (H.S.side m p) k K S l)
variable (S₁:Syllabus H N p m A R γ)
variable (P1:Paper (H:=H) (N:=N) (p:=p) (m:=m) D A F₁ K k S l s s') (i:F.Index)
-- occupations.Color code
local notation "pX"=> (H.rep N p (m+1))
variable (w:ℕ){A0:ℝ}(t:ℕ→ℕ→ℝ) -- t.Error costs per predictor query
variable (C:TariffX)(hx:Works D A (H.rep N p (m+1)) (H.rep N p m) w U T (Real.sqrt (H.levels.clock.forcedAllowance m)) C)(hp:F.coeffSize (Vinca.unitP F H p m|>.x) ≤ C.token.issue)
variable (hz:R.support=(F₁ 0).support)(hX:∀ i,i≤K→ ∀ j, (H.rep N p (m+1)).p.supBounds 0 (R.support j) (R.regular j - (F₁ i|>.regular j)) (t i j)) -- explicit
local notation "Oq"=> (H.rep N p m)
local notation "q0"=> (Vinca.coins H N p m A U R S₁ i)
local notation "q1"=> (Drift.emit D A R U T S₁ P1 i)
local notation "X"=> (pX|>.p)
set_option quotPrecheck false

local notation "uZ" => (Drift.slipsQ D A R S₁ P1 t C)
local notation "Xr" => C.token.reader
local notation "Xy"=> C.token.opener


noncomputable def auction (j:ℕ)(hj:j ≤ K) : Coefficient F (H.S.side m p):= Extra.Histories.merge (code _) (emit D A R U T S₁ P1 i j hj)
-- Produce expenditures for every eligible row.A aggregator only genuine.Foreground from Scroll.
variable {y:ℕ→ℝ}
variable (j:ℕ)(hv:j ≤ K) (ht: SumBudget (fun i=> (H.rep N p (m+1)).p.mass (R.support i) (S₁.a i)) A0)
variable (ha:∀ j,j ≤ K→ SumBudget (fun q=> (H.rep N p (m+1)).p.mass (R.support q) (t j q)) (y j))
local notation "ρj"=> (Drift.peakAt D A R S₁ P1 t C j)
local notation "xQ"=> C.token.rare
local notation "cZ"=> C.token.issue
include ht ha hv
lemma rootSlips : ∃ c0:ℝ, HasSum (Drift.slipsQ D A R S₁ P1 t C j) c0 ∧ c0 ≤ C.slip A0 s s' y j:=by
    -- edit s' shadow.
    let Z:= (H.rep N p (m+1)).p
    let F4 i:= Z.mass (R.support i) (S₁.a i); let F1 i q:= Z.mass ((F₁ 0).support q) ((P1.scroll q).price i); let F2 i q:= Z.mass ((F₁ 0).support q) ((P1.scroll q).incline i); let F3 i q:= Z.mass (R.support q) (t i q)
    let z' i:=∑' q,F1 i q; let z i:=∑' q,F2 i q; let t' i:=∑' q,F3 i q
    have hP (i)(hq:i≤K): SumBudget (F1 i) (s i):= P1.funds _ hq; have hS i (hq:i<K): SumBudget (F2 i) (s' i):= P1.grant _ hq
    have hx i (hq:i≤K): SumBudget (F3 i) (y i):= ha i hq
    refine ⟨C.slip (∑' q,F4 q) z' z t' j,C.streams j (show HasSum F4 _ from ht.2.1.hasSum) (fun i hi=> show HasSum (F1 i) (z' i) from (hP i (hi.le.trans hv)).2.1.hasSum) (fun i hi=> show HasSum (F2 i) (z i) from (hS i (hi.trans_le hv)).2.1.hasSum) (show HasSum (F3 j) (t' j) from (hx j hv).2.1.hasSum),?_⟩
    exact C.climb j ht.2.2 (fun i hi=>(hP i (hi.le.trans hv)).2.2) (fun i hi=>(hS i (hi.trans_le hv)).2.2) ((ha j hv).2.2)
-- exports.AS
lemma crestZ : ∃ a:ℝ, HasSum (Drift.peakAt D A R S₁ P1 t C j) a∧ a ≤ C.peak A0 s s' y j:=by
    obtain ⟨b,hb,hQ⟩:= Drift.rootSlips D A R S₁ P1 t C j hv ht ha -- args
    have hs:= (ht.2.1.hasSum.mul_left C.token.opener); have h: HasSum (Drift.peakAt D A R S₁ P1 t C j) (cZ+(C.token.opener*(∑' i,(pX|>.p.mass (R.support i) (S₁.a i)))+b+0)):= added (hs.add hb) hasSum_zero; rw [add_zero] at h
    exact ⟨_,h, add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left ht.2.2 C.token.fOpen) hQ)⟩ -- inference
variable (q:ℕ→ℝ) (ν:ℕ→ℝ) (hq:SumBudget (fun i=> (H.rep N p (m+1)|>.p.mass (((H.rep N p (m+1)).activities.forced i).support) (q i))) (ν j)) (hC:∀ i:ℕ,0≤q i∧∀ V':Config G (H.S.side (m+1) p), ‖R.forced i V'‖≤ q i)
include hq
lemma valleyZ : ∃ a:ℝ,HasSum (Drift.valley D A R S₁ P1 t C j q) a∧ a≤ C.delta A0 s s' y ν j:=by
    obtain ⟨b,hb,hP⟩:=Drift.rootSlips D A R S₁ P1 t C j hv ht ha; let u:ℝ:=∑' i,(pX|>.p.mass (R.support i) (S₁.a i)); let v:ℝ:=∑' i,(pX|>.p.mass (((pX).activities.forced i).support) (q i)); let g:=C.token.reader; let c:= C.token.flag
    have h: HasSum (Drift.valley D A R S₁ P1 t C j q) (xQ+(g*u+b+c*v)):= added ((ht.2.1.hasSum.mul_left g).add hb) (hq.2.1.hasSum.mul_left c)
    rw [← add_assoc] at h; exact ⟨_,h,add_le_add (add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left ht.2.2 C.token.fReader) hP)) (mul_le_mul_of_nonneg_left hq.2.2 C.token.fFlag)⟩
local notation "VZ"=> Drift.auction D A R U T S₁ P1 i
local notation "R'0"=> Vinca.issue H N p m A U R S₁ i -- merge
include hx hp hz hX hC
lemma ballet : Exhibition D l w (k j) A (H.rep N p m) R'0 (VZ j hv) κ (C.peak A0 s s' y j) (C.delta A0 s s' y ν j):=by
    obtain ⟨v,hv',hν⟩:= Drift.crestZ D A R S₁ P1 t C j hv ht ha
    obtain ⟨m',hm',he⟩:= Drift.valleyZ D A R S₁ P1 t C j hv ht ha q ν hq
    have hh α:=Drift.posts D A R U T S₁ P1 i w t C hx hp hz hX j hv q hC α; exact (River.auctions _ _ _ hh hv'.summable hm'.summable (Real.sqrt_pos.mpr (forcedPos ..))).pledge (hv'.tsum_eq.trans_le hν) (hm'.tsum_eq.trans_le he)
omit hp hC hz hX hx hv hq
lemma bridgeZ (h:j<K) : ∃ a:ℝ,HasSum (Drift.bluff D A R S₁ P1 t C j) a ∧ a≤ C.slip A0 s s' y (j+1)+C.slip A0 s s' y j:=by
    obtain ⟨b,hb,hP⟩:=Drift.rootSlips D A R S₁ P1 t C (j+1) h ht ha; obtain ⟨v,hv,hV⟩:= Drift.rootSlips D A R S₁ P1 t C j h.le ht ha
    have hp: HasSum (Drift.bluff D A R S₁ P1 t C j) (0+(b+v+0)):= added (hb.add hv) hasSum_zero; rw [add_zero, zero_add] at hp; exact ⟨_,hp,add_le_add hP hV⟩
-- need format & summability.M.S prenorm. choose use two postgres independent θ.R costs.
include hC hx hp hz hX
lemma bridgeP (y':ℕ→ℝ)(hy':∀ i:ℕ,0≤y' i∧∀ V':Config G (H.S.side (m+1) p), ‖R.forced i V'‖≤ y' i) (hv:j<K)(hK:k j ≤ k (j+1)): Patrons D l w (k (j+1)) ((H.rep N p m).p) (Vinca.decrement (VZ (j+1) hv) (VZ j hv.le)) (C.slip A0 s s' y (j+1)+C.slip A0 s s' y j) :=by
    obtain ⟨b,hb,hP⟩:= Drift.bridgeZ D A R S₁ P1 t C j ht ha hv
    obtain ⟨v,hV,hν⟩:= Drift.crestZ D A R S₁ P1 t C (j+1) hv ht ha; obtain ⟨u,hu,hU⟩:= Drift.crestZ D A R S₁ P1 t C j hv.le ht ha
    have hf α:= Drift.posts D A R U T S₁ P1 i w t C hx hp hz hX (j+1) hv y' hy' α; have hf' α:= Drift.posts D A R U T S₁ P1 i w t C hx hp hz hX j hv.le q hC α
    have h₀ α:= Drift.promotional D A R U T S₁ P1 i w t C hx hz hX j hv α
    have heα α : Patrons D l w (k (j+1)) ((H.rep N p m).p) ((q1 j hv.le) α) (ρj α):= (hf' α|>.large (v:=ρj α) le_rfl le_rfl hK le_rfl).stock
    have Ht:= River.remounted (code _) (q1 (j+1) hv) (q1 j hv.le) (Real.sqrt_pos.mpr (Extra.Histories.forcedPos H.levels m)) (fun α=> hf α|>.format) (fun α=> hf' α|>.format) (fun α=> (hf α|>.layout.symm.trans (hf' α|>.layout))) (fun α=> hf α|>.stock) heα h₀ hV.summable hu.summable hb.summable
    exact Ht.priced (hb.tsum_eq.trans_le hP)
end YM.LocalLTE.Drift

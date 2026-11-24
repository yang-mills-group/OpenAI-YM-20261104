import YM.LocalLTE.Drift.Pollen
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

include hz hX
lemma authorized (g:ℕ) (z:ℕ)(hv:z≤ K):(H.rep N p (m+1)).p.supBounds 0 ((F₁ 0).support g) (R.regular g - (P1.scroll g).potentials z) (t z g):=by rw [P1.delivers z hv g,← hz]; exact hX _ hv g
-- Need layout X= Xsupport.Face cast not free.
omit hz hX
variable (g:ℕ)
variable (a:ℝ)
include hx hz hX
local notation "Ω"=> (R.support g)
local notation "T0"=> (P1.scroll g)
-- single release.Listing at Reg costs.Exact occurrences.
lemma holds : let _B:=(F₁ 0).support g; let _:=R.regular g; let _a:=S₁.a g
       (∀ j,∀ hj:j≤K, Exhibition D l w (k j) A (H.rep N p m) (q0 (.inr (.inl g))) (q1 j hj (.inr (.inl g))) κ (Drift.peakAt D A R S₁ P1 t C j (.inr (.inl g))) (Drift.valley D A R S₁ P1 t C j 0 (.inr (.inl g)))) ∧
       ∀ j,∀ hj:j<K, Patrons D l w (k (j+1)) ((H.rep N p m).p) (Vinca.decrement (q1 (j+1) hj (.inr (.inl g))) (q1 j hj.le (.inr (.inl g)))) (Drift.bluff D A R S₁ P1 t C j (.inr (.inl g))):=by
    intro L f a'; have hp : RegFit (H.rep N p (m+1)) 0 d A (Ω) f:= ⟨S₁.outfit.smooth g,S₁.outfit.origin g,S₁.outfit.identity_null g,S₁.outfit.projects g⟩
    have he: L=R.support g:=congr_fun hz.symm _; have hB:(H.rep N p (m+1)).p.supBounds 0 (Ω) f a':=S₁.fields g
    have hu: RegFit (H.rep N p (m+1)) 0 d A L f:= he.symm ▸ hp
    have hℓ:(H.rep N p (m+1)).p.supBounds 0 L f a':= he.symm ▸ hB
    have hf:= hx.exports L (P1.scroll g) f a' hu hℓ (fun j=>t j g) (Drift.authorized D A R P1 t hz hX g) -- order
    let Tq : Coefficient F V:= q0 (.inr (.inl g))
    have hT: Tq=U.reader f L a' hu hℓ:=by change U.reader f (Ω) a' hp hB=_; congr 1; exact he.symm -- likely solves.
    have ht(j:ℕ): uZ j g=C.slip (pX|>.p.mass L a') (fun i=>pX|>.p.mass L ((P1.scroll g).price i)) (fun i=>pX|>.p.mass L ((P1.scroll g).incline i)) (fun i=>pX|>.p.mass L (t i g)) j:=by
        unfold Drift.slipsQ; rw [congr_fun hz _]
    constructor
    · intro j hj
      change Exhibition _ _ _ _ _ _ Tq _ _ ((C.token.opener * ((pX).p.mass (Ω) a'))+(uZ j g)) ((C.token.reader*((pX).p.mass (Ω) a'))+ uZ j g); rw [hT,ht,show R.support g=L from he.symm]; exact hf.loans j hj
    intro j hj; change Patrons D l w (k (j+1)) _ _ (uZ _ g+ uZ _ g); rw [ht,ht]; exact hf.stain j hj
-- high K and anchor.T.
variable (j:ℕ)(hv:j≤K)
omit hx hz hX
variable (q:ℕ→ℝ)(hC:∀ i:ℕ,0≤q i∧∀ V':Config G (H.S.side (m+1) p), ‖R.forced i V'‖≤ q i)
local notation "F1"=> (Drift.peakAt D A R S₁ P1 t C j)
local notation "F2"=> (Drift.valley D A R S₁ P1 t C j q)
private lemma primaryS {l:ℝ} {v:F.Coeff} {x μ:ℝ}(h:F.coeffSize v≤x)(hu:0<μ) : Exhibition D l S K A (H.rep N p m) (Extra.Histories.primary 0 v) (Extra.Histories.primary 0 v) μ x 0:= River.appraise (River.patronC h rfl rfl) (Extra.Histories.primary_format ..) hu
include hx hp hz hX hv hC
lemma posts (r:InputColumn.Listing) : Exhibition D l w (k j) A (H.rep N p m) (q0 r) (q1 j hv r) κ (Drift.peakAt D A R S₁ P1 t C j r) (Drift.valley D A R S₁ P1 t C j q r):=by
    have hκ:0< Real.sqrt (H.levels.clock.forcedAllowance m):= Real.sqrt_pos.mpr (forcedPos ..)
    rcases r with v|r|r
    · change Exhibition _ _ _ _ _ _ (if i=0 then _ else _) (if i=0 then _ else _) _ _ _
      by_cases ht:i=0; swap; · rw [if_neg ht,if_neg ht]; exact hx.births _ hv i ht
      rw [if_pos ht,if_pos ht]; exact Exhibition.pledge (Drift.primaryS (H:=H) (m:=m) (p:=p) (N:=N) D A hp hκ) le_rfl C.token.fRare
    · -- use price binder 0 lemma balanced defeq.
      exact Drift.holds D A R U T S₁ P1 i w t C hx hz hX r|>.1 j hv
    have he:= hC r; let b:=C.token.flag*(pX|>.p.mass ((pX).activities.forced r).support (q r))
    change Exhibition _ _ _ _ _ _ (q0 _) (Ticket.idle F ((q0 _).support)) _ 0 b; have hζ:0≤b:=mul_nonneg C.token.fFlag (mul_nonneg (Real.exp_nonneg _) he.1)
    by_cases hz:R.forced r=0
    · unfold Vinca.coins consist; simp only [Sum.elim_inr]; rw [if_pos hz]; have hf : F.coeffSize 0 ≤ 0:=by simp [Frame.coeffSize]
      exact (Drift.primaryS (H:=H) (m:=m) (p:=p) (N:=N) D A hf hκ).pledge le_rfl hζ -- definitional.
    unfold Vinca.coins consist; simp only [Sum.elim_inr]; rw [if_neg hz]; exact hx.cares _ hv _ _ _ _ hz _ _ he.2
omit hp hC hv
lemma promotional (hv:j<K) (r:InputColumn.Listing) : Patrons D l w (k (j+1)) ((H.rep N p m).p) (Vinca.decrement (q1 (j+1) hv r) (q1 j hv.le r)) (Drift.bluff D A R S₁ P1 t C j r):=by
    rcases r with v|r|r; exact River.quietCredit; exact Drift.holds D A R U T S₁ P1 i w t C hx hz hX r|>.2 j hv; exact River.quietCredit
end YM.LocalLTE.Drift

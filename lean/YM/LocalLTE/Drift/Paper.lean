import YM.LocalLTE.Drift.Purse
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
structure Paper (F₁:ℕ→ Coefficient F (H.S.side (m+1) p))(K:ℕ)(k:ℕ→ℕ)(S:ℕ)(l:ℝ)(s η: ℕ→ℝ) where
    scroll j : Drift.Papyrus D A (H.rep N p (m+1)) k K ((F₁ 0).support j) S l
    funds i : i≤K→ SumBudget (fun j=> (H.rep N p (m+1)).p.mass ((F₁ 0).support j) ((scroll j).price i)) (s i)
    grant i : i<K→ SumBudget (fun j=> (H.rep N p (m+1)).p.mass ((F₁ 0).support j) ((scroll j).incline i)) (η i)
    delivers i: i ≤ K → ∀ j,(scroll j).potentials i=(F₁ i).regular j
variable {l π:ℝ}{s η: ℕ→ℝ}
-- Producer on Exhibition receipts; this is per-axis. Uses stencil already at support. 
variable (R : Coefficient F (H.S.side (m+1) p))
local notation "Pa"=> Drift.Paper (H:=H) (N:=N) (p:=p) (m:=m) D A F₁ K k S l s η
local notation "Rp"=> (H.rep N p (m+1))
lemma scrolls {e : ℕ→ℝ}(h:∀ i, i≤K→ Exhibition D l S (k i) A (H.rep N p (m+1)) R (F₁ i) π (s i) (e i)) (hv:∀ i,i<K→ Patrons D l S (k (i+1)) ((H.rep N p (m+1)).p) (Vinca.decrement (F₁ (i+1)) (F₁ i)) (η i)):
    Nonempty (Paper («H»:=H) (N:=N) (p:=p) (m:=m) D A F₁ K k S l s η):=by
   choose q hQ hF using fun (i:ℕ) (hi:i≤ K)=> (h i hi).stock.regular
   choose a ha ht using fun (i:ℕ) (hi:i<K)=> (hv i hi).regular
   let f:=F₁ 0; let X:= f.support; have hp (j:ℕ)(hj:j ≤ K): (F₁ j).support=X:= (h j hj|>.layout).symm.trans (h 0 (Nat.zero_le _)|>.layout)
   let s0 (j i):= if H:i≤K then q i H j else 0; let μ (j i):= if hi:i<K then a i hi j else 0
   have hR (i:ℕ)(hj:i≤K): (F₁ i).Format 0 A Rp:= (h i hj).format
   let T0 (j:ℕ): Drift.Papyrus D A Rp k K (X j) S l:= {
      potentials i := (F₁ i).regular j
      price:=s0 j
      incline:= μ j
      reg i hi := by rw [← hp _ hi]; exact ⟨(hR i hi).smooth j,(hR i hi).origin j,(hR i hi).identity_null j,(hR i hi).projects j⟩
      fee i hi:= by rw [←hp _ hi, (show s0 j i=q i hi j from dif_pos hi)];exact hF i hi j
      grant i hi:= by rw [←hp (i+1) hi, (show μ j i=a i hi j from dif_pos hi)]; exact ht i hi j }
   refine ⟨T0,fun i hi=>?_,fun i hi=>?_,fun _ _ _=>rfl⟩
   · change SumBudget (fun j=>(Rp|>.p).mass (X j) (s0 j i)) (s i); simp_rw [←hp _ hi, s0,dif_pos hi]; exact hQ i hi
   change SumBudget (fun j=>(Rp|>.p).mass (X j) (μ j i)) (η i); rw [← hp (i+1) hi]; simp_rw [μ,dif_pos hi]; exact ha i hi
end YM.LocalLTE.Drift

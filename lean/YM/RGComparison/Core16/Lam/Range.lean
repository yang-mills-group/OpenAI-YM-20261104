import YM.RGComparison.Core16.Lam.Replay
/-!
# Uniform top seam `rank`, copies. Σ deadlines period from formal Step continuity, not via UV cylinder assumption.
Meter γ≤Cσ in RANK model (small, not negative norms). Momentum averaging further handled in `...`; Mask ℓ quads allocated separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk Stage Push.Uniform Push.AbsoluteSums.Animals
open PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{C F c f:Side}{P: Patch}{K:KernelChoices}{d:f.val=c.val*P.L.val}{E:F.val=C.val*P.L.val}{a:ℕ}
    {W:Oven P}{X:Shelf G (PlaqAxes⊕Axis) W.Xways}
variable (hW:P.Branches K G)(pW:Parcel.Oven.Offers W X K)
    {B : Forest (StepData.mk P K d).ratio}{B':Forest (StepData.mk P K E).ratio} (hA:C.val=c.val*a) (hB:2≤ c.val) (H: Bid.Larger (G:=G) (StepData.mk P K d)) (H' : Bid.Larger (G:=G) (StepData.mk P K E)) (V:Pinnage (zoom E d hA) B' B)(h : 2* X.sector.b<f.val)
local notation "S"=> StepData.mk P K d
local notation "K0"=> gear S B X
local notation "A0"=> StepData.mk P K E
local notation "K1"=> gear A0 B' X
set_option quotPrecheck false
local notation "∂F"=> projectStem (zoom E d hA) V
local notation "∂L"=> (show c.val∣ C.val from ⟨a,hA⟩)
local notation "T₀"=> heave (G:=G) ∂L

abbrev Letter (G:Gauge):= Axis × G.ColorIndex
def needCashR {I : Type}[Fintype I] {L:Type}[Fintype L] (F:I→ (L → G.Color)→ℝ) (X : Shelf G (PlaqAxes⊕Axis) W.Xways)(r : ℕ) := ∑ i, |lint (F i) 0 r X.Q|
lemma needed {I L: Type}[Fintype I][Fintype L](F:I→(L → G.Color)→ℝ)(X : Shelf G (PlaqAxes⊕Axis) W.Xways)(r : ℕ) : (∀ i, lint (F i) 0 r X.Q ≤ needCashR F X r)∧ 0≤ needCashR F X r:= ⟨fun i=>(le_abs_self _).trans (single_le_sum (f:=fun i=>|lint (F i) 0 r X.Q|) (fun _ _=>abs_nonneg _) (mem_univ i)), sum_nonneg fun _ _=>abs_nonneg _⟩

variable (i j:Operand G C)
include hA
private lemma tip_code (hx:separation i.1.1 j.1.1<c.val): tier (T₀ i) (T₀ j)=tier i j:= by
    have hp : (splitter ∂L i.1.1,i.1.2)=(splitter ∂L j.1.1,j.1.2) ↔ i.1=j.1:=by refine ⟨fun h=>Prod.ext (Deck.tiniest ∂L (Prod.mk.inj h).1 hx) (Prod.mk.inj h).2, fun h=>?_⟩; rw [h]
    unfold tier; have hz : (T₀ i).1=(T₀ j).1↔ i.1=j.1:=hp; simp_rw [hz]; rfl
variable (m r:ℕ)(u:ℝ)(Y:Good X)
def Exact (K:KernelChoices)(X:Shelf G (PlaqAxes⊕Axis) W.Xways)(r:ℕ)(Y:Good X)(u:ℝ) :=
   let h:=needCashR (tileΨ W K) X r; let s:=needCashR (heatΨ W K) X r; let v:= needCashR (hearth W K) X r; let l:= blank X Y r r * h
   u*s+(u*v+(r+1:ℝ)*(2*l*h*u))
omit hA in
lemma bona (Y:Good X) (K:KernelChoices){u:ℝ}(hp:0≤u): 0≤Exact K X r Y u:=by let V:= W; unfold Exact; dsimp only; have h:= (needed (tileΨ W K) X r).2; have hx:= (needed (heatΨ W K) X r).2; have he:= (needed (hearth W K) X r).2; have hv:0≤ blank X Y r r:= blank_nn ..; positivity

variable {u} (hu:0 ≤ u) (hU:Reel X u r r) (x: Site F)
include H H' V hB h pW
include hu hU x
variable (he:separation x (hold (StepData.mk P K E) i.1.1)+m+X.sector.b≤ f.val/3)
   (hv:separation x (hold (StepData.mk P K E) j.1.1)+m+X.sector.b≤ f.val/3) (k:ℕ)

include he
lemma bud_cover {k} (hk:k≤r):|nth k (bud W X B' i)-nth k (bud W X B (T₀ i))| ≤ u/costLamp X m * needCashR (tileΨ W K) X r:=by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left ((needed (tileΨ W K) X r).1 (profileDatum i)) (div_nonneg hu coin_pos.le)); unfold bud; rw [incline hA hB V h i]; exact cover_earn pW hA hB H H' V h hu hU (housed pW B' H' i).2 hk x _ (extent' (X:=X) x i he)
lemma smooth_cover {k} (hk:k≤r)(hx:separation i.1.1 j.1.1 < c.val):|nth k (smooth W X B' i j)-nth k (smooth W X B (T₀ i) (T₀ j))| ≤ u / costLamp X m * needCashR (heatΨ W K) X r:=by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left ((needed (heatΨ W K) X r).1 (tier i j)) (div_nonneg hu coin_pos.le)); unfold smooth; rw [tip_code hA i j hx,incline hA hB V h]; exact cover_earn pW hA hB H H' V h hu hU (housed pW B' H' i).2 hk x _ (extent' x i he)

omit hA H' he V hB h hu hU x in
lemma billing (i:Operand G c) {k} (hk:k≤r):|nth k (bud W X B i)| ≤ blank X pW.good r r *needCashR (tileΨ W K) X r:=by
    refine le_trans (owner_cost (blank_nn r r) pW.good.thick.1.le ((housed pW B H i).2) hk (fun l hl j hj f => coupon pW.good (paint S B pW H) r r j hj ((length_bound (harp B X i) f).trans hl))) (mul_le_mul_of_nonneg_left ((needed (tileΨ W K) X r).1 (profileDatum i)) (blank_nn ..))

include hv
local notation "Q!"=> Silk.woven
set_option maxHeartbeats 400000 in
lemma smooth_earn (hk:2+k≤r) (hr:separation i.1.1 j.1.1 < c.val): |nth k (pokes W X B' i j)- nth k (pokes W X B (T₀ i) (T₀ j))| ≤ Exact K X r pW.good u / costLamp X m:= by
    let a:= T₀ i; let b:= T₀ j 
    let F:= tileΨ W K (profileDatum i); let G':= tileΨ W K (profileDatum j); let ψ:=Silk.unite F G'
    let I:= (K1).soil (.inr i.1); let J:= (K1).soil (.inr j.1); let A:= stamps K1 (Q! (harp B' X i) (harp B' X j)) ψ; let y:=costLamp X m; let φ:=needCashR (hearth W K) X r; let z:=u/y; let Z:=needCashR (tileΨ W K) X r; let L:=blank X pW.good r r * Z
    have hx:0≤z:=div_nonneg hu coin_pos.le; let Y:= stamps K0 (Q! (harp B X (T₀ i)) (harp B X (T₀ j))) ψ; let s:=2+k
    have ht: |nth s A-nth s Y|≤ z*φ:= by
       refine le_trans ?_ (mul_le_mul_of_nonneg_left ((needed (hearth W K) X r).1 (profileDatum i,profileDatum j)) hx)
       unfold A Y; rw [incline hA hB V h, incline hA hB V h (X:=X), show Q! (cover (harp B' X i) ∂F) (cover (harp B' X j) ∂F) = cover (Q! (harp B' X i) (harp B' X j)) ∂F from ?_] -- binder
       swap
       · funext p; cases p <;> rfl
       exact cover_earn pW hA hB H H' V h hu hU (coveredBy (Z:=I) (W:=J) _ _ (housed pW B' H' i|>.2) (housed pW B' H' j|>.2)) hk x ψ (fun k hk=> (Finset.mem_union.mp hk).elim (fun he' => extent' x i he _ he') (fun hh=> extent' x j hv _ hh))
    have ha:=smooth_cover pW hA hB H H' V h i j m r hu hU x he (by omega : k≤r) hr
    have hZ:=robot_difference hk (V:= bud W X B a) (U:=bud W X B' i) (W:=bud W X B' j) (Z:=bud W X B b) (fun i hi=> billing pW H r a hi) (fun k hk=> bud_cover pW hA hB H H' V h i m r hu hU x he hk) (fun i hi=>billing pW H' r _ hi) (fun k hk=> bud_cover pW hA hB H H' V h j m r hu hU x hv hk)
    rw [order_bill, order_bill,sub_sub_sub_comm]; refine (abs_sub ..).trans ((add_le_add ha ?_).trans_eq (?_: (z*needCashR (heatΨ W K) X r)+(z*φ+(r+1:ℝ)*(L*(z*Z)+z*Z*L)) = Exact K X r pW.good u / costLamp X m))
    · change |nth s (A-bud W X B' i *bud W X B' j)-nth s (Y-bud W X B a *bud W X B b)| ≤ _; unfold nth; rw [map_sub,map_sub,sub_sub_sub_comm]; exact (abs_sub ..).trans (add_le_add ht hZ)
    unfold φ z L Z Exact y; dsimp only; ring
end YM.RGComparison.Core16.Lam

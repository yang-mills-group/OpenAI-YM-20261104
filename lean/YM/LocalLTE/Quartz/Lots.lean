import YM.LocalLTE.Quartz.Tapes
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove
open PhysicalNext.Repeat.East
-- Maneuvers depend on V generic. Carrier.P.Slot all.S.Fin count.Bound independent periods.
variable (φ':Veil c f→ℝ) (h':∀ i,0≤φ' i) (rA:ι→ℝ) (hr:∀ i,0≤rA i)
local notation "Y'"=> betaF G t L
local notation "Ω"=> Merge.Tickets (Merge.Palette.sign M S)

abbrev Stars (H:Cash W t μ L Q o a T R) (M:ι→Lotus.Leaf R):= Σ p:H.fragrances,Oscars M p
abbrev Steps (H:Cash W t μ L Q o a T R) (M:ι→Lotus.Leaf R)(n:ℕ):= Tuple H.ThinP n × (Option (Fin n)→ Tickets (Merge.Palette.sign M S))
def sift (p:ℕ)(Q:Steps H M p):Stars H M := ⟨⟨p,Q.1⟩,Q.2⟩
def beryl (P:Stars H M):= |Field.speedΛ H P.1.2| * canvasX M H P.1 P.2 φ'* pearl P.1 M rA P.2
include hr h'
lemma charmNN (P:Stars H M): 0 ≤ beryl M H φ' rA P:= mul_nonneg (mul_nonneg (abs_nonneg _) (prod_nonneg fun _ _=> mul_nonneg (Team.profit _) (prod_nonneg fun i _=> h' i))) (prod_nonneg fun _ _=> prod_nonneg fun i _=> hr i)
variable  {W' V:ℝ} (u:Site c)(ht:let Y := neighbors (East.stagnate q Q.halo*(radiusB t)) u; SumBudget (fun i=> if traceO S R i ∈Y then φ' i else 0) V) (hp : SumBudget (Merge.Palette.wages M rA) W') -- Term Stage.B' unresolved.L.
include ht hp
set_option maxHeartbeats 400000 in
lemma visits (p:ℕ) :
    SumBudget (fun z:Steps H M p=> if u∈ reachability (H:=H) ⟨p,z.1⟩∧ Candor M ⟨p,z.1⟩ z.2 q n r₀ A' then Fan.beryl M H φ' rA (Fan.sift M H p z) else 0) (East.tonic p *((rack V q*rack W' q)^(p+1))):=by
   let P:= Steps H M p; let R'α:=Option (Fin p)
   let a' (i:P):= i.1; let b' (i:P):=i.2; let Q' (i:P):Prop:=u∈ Captain.reachability (H:=H) ⟨p,i.1⟩∧ Candor M ⟨p,i.1⟩ i.2 q n r₀ A'
   let K(i:P): R'α → Finset (Veil c f) × Ω:= fun j=> (quietR M (a' i j) (b' i j), b' i j)
   have hs(i:P)(he:Q' i)(j:R'α):= Fan.weaving M H ⟨p,a' i⟩ (b' i) q n r₀ A' he.2 j
   have hk: Set.InjOn K {i|Q' i}:=by
       intro i hi j hj h; change Q' i at hi; change Q' j at hj
       have hx u: (K i u).2=(K j u).2:= congr_arg Prod.snd (congr_fun h u)
       apply Prod.ext; swap; · exact funext hx
       funext v; apply Subtype.ext
       let A (i:P):= (K i v).2.reach; have he (i:P) (h:Q' i): (i.1 v).val= Fan.arm (K i v).1 ∪ (A i):=by
          rw [← show (i.1 v).val \ A i= Fan.arm (K i v).1 from hs i h v|>.2.2]
          exact Eq.symm (sdiff_union_of_subset (h.2.lives _))
       rw [he i hi,he j hj]; unfold A; rw [h]
   let f₀ i:= if East.traceO S R i∈ neighbors (stagnate q Q.halo* radiusB t) u then φ' i else 0
   let V'(P:Ω):ℝ:= if P.val.card ≤ q then ∏ j∈ P.val,wages M rA j else 0
   let L'(D:Finset (Veil c f)):= if D.card ≤ q then ∏ i∈D,f₀ i else 0
   have he:SumBudget V' (rack W' q):=budget_pull (Subtype.val (p:= Draft (Merge.Palette.sign M S))) Subtype.val_injective (budget_grace q hp) -- edit
   have hy:SumBudget L' (rack V q):= budget_grace q ht
   let z' (i: R'α → Finset (Veil c f) × Ω):= ∏ j,L' (i j).1 * V' (i j).2
   have hB:= budget_seat (budget_prod hy he) (Option (Fin p)); rw [Fintype.card_option,Fintype.card_fin] at hB
   have hg:= budget_scale (endowed p) (East.indicatorPull K hk z' hB)
   refine budget_mono hg (fun i=> ?_) (fun i=> ?_)
   · split; exact Fan.charmNN M H φ' h' rA hr _; rfl
   change (if Q' i then beryl M H φ' rA (Fan.sift M H p i) else 0) ≤(East.tonic p:ℝ)*(@ite ℝ (Q' i) (Classical.propDecidable (Q' i)) (z' (K i)) 0); by_cases H': Q' i
   swap; · simp_rw [if_neg H',mul_zero]; exact le_rfl
   rw [if_pos H', if_pos H']
   let T (j):=K i j; let u' : H.fragrances:= ⟨p,i.1⟩; let Qd:= East.docket H ⟨p,a' i⟩; let Y:= b' i
   have he'(j:R'α)(p:Veil c f) (h:p∈(T j).1): f₀ p=φ' p:= if_pos ((neighbors_mem ..).2 (East.speaker H u' q H'.2.can _ p (hs i H' j|>.1 h) _ H'.1))
   have hW (j:R'α): L' (T j).1=∏ i∈ (T j).1,φ' i:=by unfold L'; rw [if_pos ((card_le_card (hs i H' j|>.1)).trans (H'.2.can.each j|>.received))]; exact prod_congr rfl (he' j)
   have hc(j:R'α): V' (T j).2=(Palette.team M (Y j)).weight*∏ k∈(Y j).val,rA k:=by unfold V'; rw [if_pos (hs i H' j|>.2.1),Palette.worth]; unfold Palette.wages; rw [prod_mul_distrib,mul_comm]; -- edit rfl
   have ht : z' (K i)= (canvasX M H u' (i.2) φ')* pearl u' M rA i.2:= by
      unfold canvasX pearl; rw [← prod_mul_distrib]; refine Finset.prod_congr rfl fun v _=>?_ ; change L' (T v).1* V' (T v).2=_; rw [hW,hc]; unfold T K Y b' a' u'; dsimp; ring_nf
   let P':= pearl u' M rA i.2; have hh:0 ≤ P':=prod_nonneg fun j _=> prod_nonneg fun i _=> hr i
   unfold beryl; rw [mul_assoc]; apply le_trans (mul_le_mul_of_nonneg_right (East.ballads ..) (mul_nonneg (prod_nonneg fun i _=>mul_nonneg (Team.profit _) (prod_nonneg fun i _=> h' i)) hh)); exact le_of_eq (congr_arg (_* ·) ht.symm)
end YM.LocalLTE.Fan

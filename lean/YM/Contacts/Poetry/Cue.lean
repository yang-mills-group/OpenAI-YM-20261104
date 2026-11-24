import YM.Contacts.Poetry.Petals
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Term
/-! Adapted from Meadow/{Fir, Oriole, Duet}. Expenses at provisional & refuel. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j n₀ m₀ m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
open Meadow (spin garnerAt garner share portions regularA nonnegative paysOne honor melody ripened burgeoning arc_receipt arc bough spurs  Rags legs rollers)
variable {Ξ:Lecturer R' m₀}{Ξ₀:Lecturer R m₀}
open Meadow (Budget)
variable (n₀ I Ξ χ)(β γ:ℝ)
def tower (i:Magazine I): Config G c→ℝ:= if Poetry.keep I Ξ n₀ i then arena I χ β γ i else 0
def hKeep (t : ℕ) (z:Magazine I) := if z∈Poetry.bouquet I Ξ n₀ t then 0 else arena I χ β γ z

def timbres (t:ℕ): Collection.Source G c:= ⟨choir (hKeep n₀ I χ Ξ β γ t) ∘ pennant I, fuse I (Terrain.runway I) χ ∘ Refrain.badge I⟩

lemma compass (k:ℕ) (x: ℕ) : (timbres n₀ I χ Ξ β γ k|>.logRead x) = (if (pennant I x).2 ∈ Poetry.bouquet I Ξ n₀ k then 0 else (gallery I χ β γ).logRead x):= by
  unfold timbres gallery choir; let y:= Song.pennant I x; change Rim c • ((if _ then (_:Config G c→ℝ) else _) ∘ y.1.view)= _; split
  · ext; simp
  rfl

variable (p':BudgetPoint) (ht:p'.B=radiusB p)
include ht in
lemma tone (δ b : ℝ) {k v u : ℝ} (h : T.down.Bounds T.low k v u) (he : WilsonStartup.Decent T.low p') (hs: preExponent p'/p'.B≤ k/4) (hb : Real.exp (-(k/4)*p'.B)*Song.octaveNeed G p' T.low k v u β γ ≤ b) (hP : Budget p' (Beam.dashboard I) (fun i:I.fragrances=> Poetry.tower n₀ I χ Ξ β γ (.inl i)) δ):
    Budget p' (Beam.contents I p') (Poetry.tower n₀ I χ Ξ β γ) (δ+b) := by
  obtain ⟨f,hF,hV⟩:= hP; obtain ⟨k',hK,hP⟩:= Meadow.lent (c:=c) p' _ _ _ γ h he hs
  have hz z:0≤k' z:=(hP z).2.1; let z i:= if B < arc T.down i then k' i else 0
  let K: Magazine I→ℝ:= Sum.elim f z; have hv i : 0 ≤ z i:= by unfold z; split; exact hz _; exact le_rfl
  refine ⟨K,fun x=>Cost.sum (hF x) (show SumBudget _ b from ?_),?_⟩
  · rw [ht] at hb
    have ht:= Meadow.arch_tail (strings T.down p') p' (arc T.down (c:=c)) hK (k:=B) (by have h:= h.width; positivity) hz x
    refine budget_loosen (budget_mono ht (fun i=> ?_) (fun i=> ?_)) hb
    · split; next h=> exact mul_nonneg (hv _) (Real.exp_nonneg _)
      exact le_rfl
    ·
      by_cases he: B< arc T.down i
      · dsimp only [Beam.contents,K]; simp_rw [Sum.elim_inr,z,if_pos he,if_pos he.le]; exact le_rfl
      dsimp only [Beam.contents,K,Sum.elim]; unfold z; rw [if_neg he]; split
      next h=> rw [zero_mul]; split_ifs <;> first | exact mul_nonneg (hz _) (Real.exp_nonneg _)| simp
      exact le_rfl
  intro i; rcases i with i|i
  · exact hV i
  unfold Poetry.tower; split; next h=> rw [show K (.inr i)=_ from (if_pos h : z i=k' i)]; exact hP i
  next h=> rw [show K (.inr i)=_ from (if_neg h : z i=0)]; exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p') (X:=(strings T.down p' i).support) (o:=(strings T.down p' i).site) 0)⟩

-- add any tower.D.Dep support + Preserved Phi.A.
lemma candles (k:ℕ) {t w : ℝ} (h : Budget p' (Beam.marquee I p').reg (choir (tower n₀ I χ Ξ β γ) ∘ pennant I) t) (hp: Budget p' (Beam.marquee I p').reg (fun i=> if debris I Ξ n₀ k i then (gallery I χ β γ).logRead i else 0) w) :
   Budget p' (Beam.marquee I p').reg (timbres n₀ I χ Ξ β γ k|>.logRead) (t+w):= by
  refine Terrain.Cap.add ?_ _ h hp
  ext x i; rw [compass]; let y:= pennant I x; let z:= y.2; let u:= y.1.view i
  change ((if z∈ bouquet I Ξ n₀ k then (_:Config G c→ℝ) else _) i)= Rim c * ((if keep I Ξ n₀ z then (_:Config G c→ ℝ) else _) u)+(if Poetry.debris I Ξ n₀ k x then (_:Config G c→ ℝ) else _) i
  by_cases he:z∈ bouquet I Ξ n₀ k; · rw [if_pos he, if_neg (notKept z he), if_neg (show ¬debris I Ξ n₀ k x from (fun h=> h.2 he))]; simp
  rw [if_neg he]; split
  next hv=> rw [if_neg (show ¬debris I Ξ n₀ k x from (fun h=> h.1 hv))]; change _= _ + 0; rw [add_zero]; rfl
  next hh=> rw [if_pos (show debris I Ξ n₀ k x from ⟨hh,he⟩)]; simp


variable (k:ℕ) (x:Site c){t v:ℝ}(hp:Collection.Local (Beam.marquee I p') p' (gallery I χ β γ) t v)
include hp ht
lemma regularW (i:ℕ) (h:i∈panel n₀ I Ξ k) : p'.Regular (neighbors (Poetry.studio X.halo B m₀ n₀) x) (garnerAt I p' x i • (gallery I χ β γ).logRead i) := by
  by_cases hF:garnerAt I p' x i=0; · rw [hF,zero_smul]; exact CouplingShape.reg_const _
  have hM:= (assigned n₀ I Ξ p' x i h ht hF).2
  exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (hp.smooth i) hM)
omit ht
lemma unearned (V:Config G c) :
    (Beam.marquee I p'|>.read (gallery I χ β γ)|>.additive p' V) = (Beam.marquee I p'|>.read (timbres n₀ I χ Ξ β γ k)|>.additive p' V) +
       ∑ i∈Poetry.panel n₀ I Ξ k, masked p'.threshold ((Beam.marquee I p').reg i).support ((gallery I χ β γ).logRead i) V:= by
  let t' i:= masked p'.threshold ((Beam.marquee I p').reg i).support ((gallery I χ β γ).logRead i) V; let h i:=if i∈ Poetry.panel n₀ I Ξ k then t' i else 0
  let f i:= ((Beam.marquee I p').read (gallery I χ β γ)).regularOccurrence p' i V; let g i:= ((Beam.marquee I p').read (timbres n₀ I χ Ξ β γ k)).regularOccurrence p' i V
  have he : g=f-h:= by
    funext i; change masked _ _ ((timbres n₀ I χ Ξ β γ k).logRead i) V=f i-h i; rw [Poetry.compass]; have hh : f i=t' i:= rfl
    rw [hh]; unfold h; split
    next hz=> rw [if_pos ((Poetry.petaled n₀ I Ξ i).2 hz),sub_self]; simp [masked]
    next hz=> rw [if_neg (mt (Poetry.petaled n₀ I Ξ i).1 hz),sub_zero]; rfl
  have hs: Summable f:= Roof.Embrasure.series _ _ hp V
  have h':HasSum h (∑ i∈ Poetry.panel n₀ I Ξ k,t' i):=by
    convert hasSum_sum_of_ne_finset_zero (s:= Poetry.panel n₀ I Ξ k) (f:=h) (fun i hi=> if_neg hi) using 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
    infer_instance
  have he': (∑' i, g i)= (∑' i, f i)-∑ i∈ Poetry.panel n₀ I Ξ k,t' i:= by rw [he]; exact (hs.hasSum.sub h').tsum_eq
  change (∑' i,f i)=(∑' i, g i)+_; rw [he',sub_add_cancel]
include ht
lemma regularY : p'.Regular (neighbors (Poetry.studio X.halo B m₀ n₀) x) (Poetry.barony n₀ I Ξ χ k β γ x):= by rw [aster n₀ I χ Ξ p' β γ k]; exact Meadow.regularA _ fun i hi=> regularW n₀ I χ Ξ β γ p' ht k x hp i hi
-- applies AFTER taking estimate on any torus hosts, sent across stars as separate estimates
omit k x -- may be omitted?
lemma refurbish {σ C' Λ d q v':ℝ} (hv:preExponent p'/p'.B≤σ/4)(hw:T.down.Bounds T.low σ C' Λ)(hh:WilsonStartup.Decent T.low p')
   (hc:Real.exp (-(σ/4)*p'.B)*Song.octaveNeed G p' T.low σ C' Λ β γ ≤ d) (hr : Terrain.Make I p' χ (fun i=> Poetry.keep I Ξ n₀ (.inl i)) q)(hm:0<v') : ∀ᶠ k in atTop, Budget p' (Beam.marquee I p').reg (timbres n₀ I χ Ξ β γ k|>.logRead) (turnFee p'*(q+d)+v'):= by
  -- grab no curve
  let P:=Beam.marquee I p'
  let u:=gallery I χ β γ
  obtain ⟨f,hf,h⟩:=hp.cheap
  have hL:Terrain.Make I p' χ (fun i=> Poetry.keep I Ξ n₀ (.inl i)) q := hr -- check decid
  have hp':= Meadow.soared p' _ (tone n₀ I χ Ξ β γ p' ht q d hw hh hv hc ?_); swap; · exact hr
  have hE:= Meadow.limits (P:=P) (h:=fun (_:ℝ)=>u) p' (Poetry.debris I Ξ n₀) 0 ⟨f,(Boulevard.planetary h (fun i=>(hf i).1)).2.1,hf⟩ (dissolved I Ξ n₀) hm
  filter_upwards [hE] with k hk; obtain ⟨f,h,hF⟩:=hk; apply candles n₀ I χ Ξ β γ p' k hp'; refine ⟨_,hF,fun i=>⟨?_,h i⟩⟩; dsimp only; split; exact hp.smooth i; exact CouplingShape.reg_const _
end YM.PhysicalNext.Repeat.Poetry

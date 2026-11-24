import YM.LocalLTE.Tile.Nap
import YM.LocalLTE.E6.Tickets
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Loft
/-! # Price post-Pure and post-Physical Log along the same path

BUDGET leaves inheritance contributions on their *actual labels*, no
truncation applied through them. Retained amounts to be supplied separately
for non-pure inputs. Doing so for a model trajectory named prior Log and
identifying coefficients with that NORMALIZED recursion has stronger premises
than this decomposition. All masks & addresses native to Cash. Auxiliary
invoice used also on charts: raw reparameterized stencil before deterministic
KLEAR. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {ℓ k j n: ℕ} {K : Teller G} {p a W U V g C' y A M K₀ r β δ q b s v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W p a L₀ X o U T R) {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain

-- Seed identity for a fixed representation (still I-phase FLAGS hold).
def intern : Alliance H H 1 0 := Match.staple rfl rfl rfl
lemma coincides (z:H.fragrances) : (intern H).furrow z=z := by
  obtain ⟨t,k⟩:=z; change ⟨t,_⟩=(⟨t,k⟩:H.fragrances); congr 1

/- `heritage H χ γ` is measured post price of ALL inherited-only
calls not zero. Deliberately not filtering by K flags. -/
def heritage (χ:Chi) (γ:ℝ) (i : Magazine H):Config G c→ℝ:= Sum.elim (fun z=> if ancestry z then opus H (intern H) χ γ (.inl z) else 0) (fun _=>0) i

/-- Pure log estimate on the `E` contributions independent of inherited
calls. `K` costs separate (not literacy). -/
def rescaleN (χ: Chi) (ℓ : ℕ) (γ : ℝ) (i : Magazine H) : Config G c→ℝ:= Sum.elim (fun z=> if ancestry z then 0 else if keepN H ℓ (.inl z) then opus H (intern H) χ γ (.inl z) else 0) (fun p=> if keepN H ℓ (.inr p) then opus H (intern H) χ γ (.inr p) else 0) i

def sortable (χ: Chi) (ℓ k : ℕ) (γ : ℝ) (i:ℕ): Config G c→ℝ:= if debrisN H ℓ k i then (plusone H (intern H) χ γ).logRead i else 0

def ash (χ:Chi) (ℓ k : ℕ) (γ:ℝ):ℕ→ Config G c→ℝ:= (choir (rescaleN H χ ℓ γ) ∘ pennant H)+ sortable H χ ℓ k γ

def heats (χ:Chi) (γ:ℝ):ℕ→ Config G c→ℝ:= choir (heritage H χ γ) ∘ pennant H

private lemma lineage (z:H.fragrances) (h:ancestry z) : keepN H ℓ (.inl z):= by
  intro hz; obtain ⟨v,hv⟩:= hz
  rw [← hv] at h; obtain ⟨i,s,hi⟩:=h; change Opacity.key S s∈hatch S (v.val.2 i) at hi
  obtain ⟨r,hr,h⟩:= Finset.mem_map.mp hi
  have hP:Beam.Pennies S (Opacity.key S s):=(penned S _).2 ⟨r,h⟩
  obtain ⟨l,he,hh⟩:=hP
  change Sum.inr (Sum.inr (Sum.inl (Sum.inl (Sum.inl s))))=_ at he; obtain rfl := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj he)); exact hh
lemma allotted (ℓ k : ℕ) : (timbresN (intern H) (χ:=χ) γ ℓ k).logRead = heats H χ γ + ash H χ ℓ k γ:= by
  funext j V; change _=(heats H χ γ j V)+(_+_); rw [compassN]
  let y:= pennant H j; let z:=y.2; let P:= (plusone H (intern H) χ γ).logRead j V; let x:= Rim c
  let t:=y.1.view V; have he:P=x*opus H (intern H) χ γ z t:= rfl
  change ((if z ∈ bouquetN H ℓ k then (0:Config G c→ℝ) else (plusone H (intern H) χ γ).logRead j) V)=x*(heritage H χ γ z t)+(x*(rescaleN H χ ℓ γ z t)+sortable H χ ℓ k γ j V)
  by_cases hp : keepN H ℓ z
  · rw [if_neg (show _ from (fun h : z∈bouquetN H ℓ k=> notKeptN z h hp)),show sortable H χ ℓ k γ j=0 from if_neg (show ¬debrisN H ℓ k j from (fun h=> h.1 hp))]
    change P=_; rw [he]; rcases hY : z with z|z
    · dsimp only [heritage,rescaleN,Sum.elim_inl]; split_ifs <;> simp
      all_goals grind
    dsimp only [heritage,rescaleN,Sum.elim_inr]; rw [if_pos (hY ▸ hp)]; simp
  suffices h: heritage H χ γ z=0∧rescaleN H χ ℓ γ z=0 by
    by_cases hi:z∈ bouquetN H ℓ k
    · rw [if_pos (show _ from hi),show sortable H χ ℓ k γ j=0 from if_neg (show ¬ debrisN H ℓ k j from (fun h=> h.2 hi)),h.1,h.2]; simp
    rw [if_neg (show _ from hi),sortable,if_pos (show debrisN H ℓ k j from ⟨hp,hi⟩),h.1,h.2]; simp
  revert hp; generalize z=z
  rintro h; rcases z with z|z
  · simp only [rescaleN,heritage,Sum.elim_inl, if_neg (show ¬ancestry z from mt (lineage H z (ℓ:=ℓ)) h), if_neg h,and_self]
  exact ⟨rfl,if_neg h⟩

lemma rep_heir (hv:∀ i U,R.activities.E i U=0) (χ:Chi)(γ:ℝ): heats H χ γ=0:= by
  have hx i:heritage H χ γ i=0:= by
    rcases i with i|i
    · dsimp only [heritage,Sum.elim_inl]; split; next h=>
        ext U; change (-1:ℝ)*stream H χ U ((intern H).furrow i)=_; rw [coincides,atHeir hv h]; simp
      rfl
    rfl
  ext i U; change Rim c* heritage H χ γ _ _=_; rw [hx]; simp
variable {p' : BudgetPoint} (h : Collection.Local (posting p' H) p' (plusone H (intern H) χ γ) t V) (hV : 0<b)

include h hV
lemma buys (ℓ:ℕ) : ∀ᶠ k in atTop,Meadow.Budget p' (Beam.marquee H p').reg (sortable H χ ℓ k γ) b := by
  obtain ⟨f,hf,hF⟩:=furlough p' (fun i=> (Beam.rewrite_rule H p' i).symm) h
  let P:ℝ→ Collection.Source G c:= fun _=> plusone H (intern H) χ γ; let R:= Beam.marquee H p'; let S m:=debrisN H ℓ m
  have hv (i:ℕ) := dissolvedN (J₀:=ℓ) H i
  filter_upwards [Meadow.limits (h:=P) (P:=R) p' S (0:ℝ) ⟨f,hf,hF⟩ hv hV] with k hk; obtain ⟨y,hy,hq⟩:=hk; refine ⟨y,hq,fun i=>⟨?_, hy i⟩⟩
  unfold sortable; split; next hK=> rw [Beam.rewrite_rule]; exact h.smooth i
  exact CouplingShape.reg_const _

omit hV h
variable (N : Captain H j C' δ v y A b r M q m χ) (hw:p'.order≤j) (hv:p'.power ≤ n)
   (ht:p'.threshold=Pressure.temp p) (hX : p'.B=Pressure.radiusB p)
    (hη:preExponent p' ≤ s) {X' : ℝ}
    (hQ : Ac.Hit (Captain.reachability (H:=H)) (radiusB p) (fun z=> if tiredN H ℓ z then N.markΦ z n else 0) s X')
include H N hQ hw hv ht hX hη
lemma rescaleShort (γ:ℝ) : Budget p' (Beam.dashboard H) (rescaleN H χ ℓ γ ∘ Sum.inl) X':= by
  let D (i:H.fragrances):= if tiredN H ℓ i then Song.sequence H (intern H) χ i else 0
  let f i:= if tiredN H ℓ i then N.markΦ i n else 0
  have h' i : p'.Regular (Beam.dashboard H i).support (D i) ∧ p'.supBounds (Beam.dashboard H i).site (Beam.dashboard H i).support (D i) (f i):= by
    unfold D f; split
    · have hk:= N.gloryBudget i p' ht hw
      rw [Beam.see, Song.reconnects H (intern H) i, coincides]; have Hz:= CouplingShape.sup_scale (-1) (hk.2.2 n hv _ (show _ from ((Beam.see H i).trans (show Song.perf H i= _ from rfl)) ▸ (Beam.dashboard H i).anchor)); rw [abs_neg,abs_one,one_mul] at Hz
      unfold Song.sequence; rw [coincides]; exact ⟨CouplingShape.reg_scale _ hk.2.1,Hz⟩
    exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p') (X:=(Beam.dashboard H i).support) (o:=(Beam.dashboard H i).site) 0)⟩
  have hB : Quotes.early p' (Beam.dashboard H) f X' := by
    intro x; refine budget_mono (hQ x) (fun i=> ?_) (fun i=> ?_)
    · split; next hz=> exact mul_nonneg (h' _|>.2.1) (Real.exp_nonneg _)
      rfl
    split
    next he =>
      have hx i: Captain.reachability i=(Beam.dashboard H i).support:= (Beam.see H i).symm
      rw [if_pos (show x∈ Captain.reachability i from he ▸ (show _ from (hx i).symm ▸ (Beam.dashboard H i).anchor)),hX,hx]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _))) (h' i).2.1
    exact (hQ x).1 i
  refine emptyFree (Beam.dashboard H) p' (u:=D) ⟨f,hB,h'⟩ _ ?_; intro i; dsimp only [rescaleN,Function.comp_apply,Sum.elim_inl]; split
  · right; rfl
  next hv =>
    split; next hk=>
      by_cases he:tiredN H ℓ i; · left; unfold D; rw [if_pos he]; rfl
      right; ext U; change (-1:ℝ)*stream H χ U _=0; rw [coincides,show stream H χ U i=0 from Classical.byContradiction (fun ne=>hk (remnantsN i he U ne hv)),mul_zero]
    right; rfl
variable {E₀ D F' Z :ℝ} (hd : T.down.Bounds T.low σ E₀ Λ) (hp : WilsonStartup.Decent T.low p') (hs: preExponent p'/p'.B ≤ σ/4) (hb: Real.exp (-(σ/4)*p'.B)*Song.octaveNeed G p' T.low σ E₀ Λ R.beta γ ≤ D)

include hd hp hs hb
lemma rescaleAll : Budget p' (Beam.contents H p') (rescaleN H χ ℓ γ) (X'+D):= by
  obtain ⟨f,hf,hF⟩:= rescaleShort H N hw hv ht hX hη hQ γ
  obtain ⟨k',hK,hP⟩:= Meadow.lent (c:=c) p' _ _ R.beta γ hd hp hs
  have hz z:0≤k' z:=(hP z).2.1; let z i:= if B < arc T.down i then k' i else 0
  let K: Magazine H→ℝ:= Sum.elim f z; have hv i : 0 ≤ z i:= by unfold z; split; exact hz _; exact le_rfl
  refine ⟨K,fun x=>Cost.sum (hf x) (show SumBudget _ D from ?_),?_⟩
  · rw [hX] at hb
    have ht:= Meadow.arch_tail (strings T.down p') p' (arc T.down (c:=c)) hK (k:=B) (by have h:= hd.width; positivity) hz x
    refine budget_loosen (budget_mono ht (fun i=> ?_) (fun i=> ?_)) hb
    · split; next h=> exact mul_nonneg (hv _) (Real.exp_nonneg _)
      exact le_rfl
    by_cases he: B< arc T.down i
    · dsimp only [Beam.contents,K]; simp_rw [Sum.elim_inr,z,if_pos he,if_pos he.le]; exact le_rfl
    dsimp only [Beam.contents,K,Sum.elim]; unfold z; rw [if_neg he]; split
    next h=> rw [zero_mul]; split_ifs <;> first | exact mul_nonneg (hz _) (Real.exp_nonneg _)| simp
    exact le_rfl
  intro i; rcases i with i|i
  · exact hF i
  dsimp only [rescaleN,Sum.elim_inr]; split; next h=> rw [show K (.inr i)=_ from (if_pos h : z i=k' i)]; exact hP i
  next h=> rw [show K (.inr i)=_ from (if_neg h : z i=0)]; exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p') (X:=(strings T.down p' i).support) (o:=(strings T.down p' i).site) 0)⟩

omit H N hQ hw hv ht hX hη hd hp hs hb in
lemma combineCost {ι:Type} (f h:ι→ Config G c→ℝ) (A:ι→ RegularAddress c)
    (hp : Budget p' A f a) (hv:Budget p' A h W) : Budget p' A (f+h) (a+W):= by
  obtain ⟨k,h',hv'⟩:=hv; obtain ⟨c',hc,hF⟩:=hp; refine ⟨c'+k,fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (hc i) (h' i) using 2 with x; dsimp only [Pi.add_apply]; split <;> ring
  have hh:(f+h) i=f i-((-1:ℝ) • h i):= by simp
  have hp:= CouplingShape.reg_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1); rw [hh]; refine ⟨hp,?_⟩
  have hb:= CouplingShape.sup_scale (-1) (hv' i).2; rw [abs_neg,abs_one,one_mul] at hb; exact CouplingShape.sup_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1) (hF i).2 hb

include h
lemma buys_ash (hq:0<F') : ∀ᶠ k in atTop,Budget p' (Beam.marquee H p').reg (ash H χ ℓ k γ) (turnFee p'*(X'+D)+F'):= by
  filter_upwards [buys H h hq ℓ] with k he
  exact combineCost _ _ _ (soared p' _ (rescaleAll H N hw hv ht hX hη hQ hd hp hs hb)) he

lemma auxRolling (hZ : ∀ i U, R.activities.E i U=0) (hq:0<F') : ∀ᶠ k in atTop, Budget p' (Beam.marquee H p').reg (Meadow.timbresN (intern H) (χ:=χ) γ ℓ k).logRead (turnFee p'*(X'+D)+F'):= by
  filter_upwards [buys_ash H h N hw hv ht hX hη hQ hd hp hs hb hq] with k he; rwa [allotted, rep_heir H hZ,zero_add]

omit N hQ hw hv ht hX hη hd hp hs hb h
lemma massHeir (hP : Collection.Local (Beam.marquee H p') p' (Height.serve H (intern H) χ (Beam.lit H)) D Z) (γ:ℝ) : Budget p' (Beam.marquee H p').reg (heats H χ γ) D := by
  obtain ⟨f,h,hF⟩:= hP.cheap; refine emptyFree _ p' (u:=fun i=>(Height.serve H (intern H) χ (Beam.lit H)|>.logRead i)) ⟨f,hF,fun i=> ⟨hP.smooth i,h i⟩⟩ _ fun i=> ?_
  let u:= pennant H i
  have hx t: (Height.skilled H (intern H) χ (Beam.lit H)) t= heritage H χ γ t ∨ heritage H χ γ t=0:=by
    rcases t with z|z
    · dsimp only [heritage,Sum.elim_inl]; split
      next ha=>
        by_cases hb:Beam.lit H z; · left; unfold Height.skilled; simp only [Sum.elim_inl,if_pos hb]; rfl
        right; ext V; change (-1:ℝ) * stream H χ V ((intern H).furrow z)= _; rw [coincides, show stream H χ V z=0 from Classical.byContradiction (fun he=>hb (Height.heir_priced ha he)),mul_zero]; rfl
      right; rfl
    right; rfl
  rcases hx u.2 with he|he
  · exact Or.inl (congr_arg (fun f=>Rim c • (f ∘ u.1.view)) he)
  right; change Rim c • (heritage H χ γ u.2 ∘ u.1.view)=0; rw [he]; ext; simp
end YM.PhysicalNext.Repeat.Meadow

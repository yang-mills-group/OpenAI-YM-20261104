import YM.LocalLTE.Slide.Rink
import YM.LocalLTE.Tile.Allot
import YM.LocalLTE.Slide.Bisque
import YM.LocalLTE.Tier.Dais
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
open Scarf Refrain Marlin
variable {χ : Chi}
-- Model flags lift. `lowers q` means BELOW cutoff inclusive, and all MODEL.
-- Grade Birth data address intrinsic. FG stores pre slot? simpler F i = natural, J+1 noise reserved.
def lowers (e:ℕ→ℕ) (k:ℕ) (v:H.fragrances): Prop:= ∀ i m,Sum.inl m∈East.docket H v i→ e m ≤ k

def lectures (j m :ℕ) (e:ℕ→ℕ) (p:H.fragrances) := East.Orchestra H p m ∧ lowers H e j p
lemma louder (e:ℕ→ℕ)(j m:ℕ){p:H.fragrances} (h:lectures H j m e p) {k:ℕ}(he:j≤k): East.lectures H k m e p:=⟨h.1,fun i m hp=> (h.2 i m hp).trans he⟩

lemma literal_cal {X':Cash W s a L X o U T R'} (A: Match.Alliance H X' 1 0)(he:A.units=Equiv.refl _) (k j ℓ:ℕ)(hr:R.path=R'.path) (hv:R.activities.reg= R'.activities.reg) (hk:R.activities.forced=R'.activities.forced) (f:ℕ→ℕ): (∀ i,lectures H j ℓ f i ↔ lectures X' j ℓ f (A.furrow i))∧
    East.locker H (lectures H j ℓ f) k=East.locker X' (lectures X' j ℓ f) k:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,P,Beta,T₁⟩:=R'
  cases hr; cases hv; cases hk; obtain ⟨_,_,_⟩:= A; cases he
  have h i: lectures H j ℓ f i ↔ lectures X' j ℓ f i:=by
    constructor
    · rintro ⟨⟨hi,hc,ha,hm⟩,hv⟩; refine ⟨⟨hi,fun i=>?_,ha,hm⟩,hv⟩; obtain ⟨he,h,hv,hk,hℓ,hp⟩:=hc i; exact ⟨he,h,hv,hk,hℓ,hp⟩
    rintro ⟨⟨hi,hc,ha,hm⟩,hv⟩; refine ⟨⟨hi,fun i=>?_,ha,hm⟩,hv⟩; obtain ⟨he,h,hv,hk,hℓ,hp⟩:=hc i; exact ⟨he,h,hv,hk,hℓ,hp⟩
  have hv : lectures H j ℓ f = lectures X' j ℓ f := funext fun i=> propext (h i)
  refine ⟨fun i=> ?_,?_⟩ -- edit
  · change _ ↔ lectures X' j ℓ f (Meadow.intern X' |>.furrow i); rw [Meadow.coincides]
    exact h _
  exact hv ▸ rfl
lemma solidAge (p:H.fragrances)(i)(k:ℕ): Sum.inl k∈ East.docket H p i↔Opacity.key S k∈ (p.2 i).val:= by unfold East.docket East.lining; exact mem_preimage
lemma inactive (p:H.fragrances)(he:¬ancestry p) (e:ℕ→ℕ) j : East.lowers H e j p:= fun i k hi=> (he ⟨i,k,(solidAge ..).mp hi⟩).elim
-- any inheritance occurrence that flows => actual label nonzero. From blaze heads.
lemma born {p:H.fragrances}{k:ℕ} {i: Option (Fin p.fst)} {U: Config G c}(he:stream H χ U p≠0)(hv:Sum.inl k∈East.docket H p i): R.activities.E k ≠0:=by
    intro hp; apply he
    have hk V : R.activities.regularOccurrence R.p k V=0 := by simp [Activities.regularOccurrence,masked,Set.indicator,hp]
    let K:=p.2 i
    have hl:Opacity.key S k∈ K.val:= (solidAge ..).1 hv
    unfold stream Gas.term; suffices hk: leaflet H χ U K=0 by rw [prod_eq_zero (Finset.mem_univ i) hk,mul_zero,zero_div]
    unfold March.leaflet Pond.likely Stained.fringe
    have hx (F:Tree.Forest S.ratio) (Y:Coat T F) J u : Polar.floating Y o.a R W X.table u J X.halo K.val=0 := by
       unfold Polar.floating; apply Finset.prod_eq_zero hl
       change Real.exp (-(R.activities.regularOccurrence _ k _) * _) -1= _; rw [hk,neg_zero,zero_mul,Real.exp_zero,sub_self]
    have hv (F:Tree.Forest S.ratio) (Y:Coat T F): Shield.shelter Y W o.a K.val R X.table X.halo=0 := by
       unfold Shield.shelter; split; next _=> unfold Shield.seating; simp only [Shield.bars,Pond.likely,hx,mul_zero,integral_zero,sum_const_zero]
       rfl
    change _ * ∑ y: Greenbelt.Reserve S, (∫ v, Shield.shelter _ _ _ K.val _ _ _ ∂ _) = _; simp only [hv,integral_zero,sum_const_zero,mul_zero]
lemma sits (p:H.fragrances)(i:ℕ) (hx:¬ Height.tiredN H ℓ p)(e:ℕ→ℕ) (hp:∀ k,e k≤ i→ R.activities.E k ≠ 0→(R.activities.reg k).support⊆neighbors (S.patch.L.val* radiusB s) (R.activities.reg k).site)(hl:East.lowers H e i p)(h:ancestry p)(V:Config G c)(hV:stream H χ V p ≠0): lectures H i ℓ e p:=by
   refine ⟨East.arises H p hx V hV h ?_,hl⟩; intro j k hk; exact hp k (hl _ _ hk) (born H hV hk)
end YM.PhysicalNext.Repeat.East

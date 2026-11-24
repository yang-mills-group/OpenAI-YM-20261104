import YM.RGComparison01.Cutback

/-!
# All leftwards terms paid. Whole-angle group back.

 Truncation number is an AFTER-period variable, existence for coordinates
 with no resulting uniformity penalty. Can ask finitely simultaneous instances.
 -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace Ports
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
variable {c f : Side} {m n N k : ℕ} (sizes : f.val=c.val*(A.B.a.S.block m).val)
    {R : RG.Rep G f} (H : Boulevard.Chartlet F.shape A N m sizes R) (Z : Ribbon R n) (Ω : ℕ→Prop)
local notation "Y" => A.B.a.budget m
local notation "O" => Chi.canonical
local notation "L" => High.countOrder k
local notation "B" => Drawing.cabinet H Z
local notation "γ" => A.B.kin.alpha N m
local notation "S" => Song.plusone H (Divides.selfA H) O γ
local notation "Y'" => Beam.marquee H Y

variable (h : Drawing.Opens Z Ω) {v : ℝ} (hv : Wet F sizes H k Ω v)
include F h sizes H
lemma ambitious (k : ℕ) (z : Magazine H) (hx : Coast.kept F sizes H Ω k z) (hp: opus H (Divides.selfA H) O γ z ≠ 0) :
    ∀ᶠ i in atTop, z ∈ (B).catalogue (High.countOrder k) i := by
  rcases z with z|z
  · have he: ¬ Selector.Inherited Ω z := fun h=> hx (Or.inr h)
    have ht: ¬ Selector.Weeds (High.countOrder k) z := fun h=>hx (Or.inl (show Divides.meter H Ω _ (Y).B (.inl z) from ⟨he,h⟩))
    have hh:∃ V : Config G c, stream H O V z ≠ 0 := by
      by_contra! h; apply hp; funext V; change -1*stream H O V ((selfA H).furrow z) = 0; rw [farther,h,mul_zero]
    obtain ⟨V,hV⟩:=hh; exact Cabinet.tides (B) _ (Drawing.permute Z Ω h O V z ht he hV)
  apply Cabinet.rains (B) (High.countOrder k) _
  by_contra! hp; exact hx (Or.inl (show Divides.meter H Ω _ (Y).B (.inr z) from hp.le))
lemma aperture (j:ℕ) (i:ℕ) (hi: i∈ (B).board (High.countOrder k) j) : (Coast.inherited F sizes H Ω).logRead i=0 := by
  let p:Magazine H:= (pennant H i).2; let K:(Magazine H→ Prop) := Divides.hires H Ω
  have hb : ¬ K p:= by
    intro hx; have hp : p∈(B).catalogue (High.countOrder k) j:=(Cabinet.earns ..).1 hi; generalize p=z at *; rcases z with z|z
    · obtain ⟨m,hm,hz⟩:= mem_map.mp (inl_mem_disjSum.mp hp); subst z; exact Drawing.vacant Z Ω ‹_› m hx
    exact hx
  exact (Coast.posts_id F sizes H _ i).trans (if_neg hb)

variable (δ : ℝ) (hd : 0 < δ)
include hv hd
lemma too_far :
    ∀ᶠ k' in atTop, Meadow.Budget Y (Y').reg (fun i=> if i ∈ (B).board (High.countOrder k) k' then 0 else (Coast.kept_out F sizes H Ω k|>.logRead i)) δ := by
  let X' := Y'; let z:= Coast.kept_out F sizes H Ω k; let P j i := i∉ (B).board L j ∧ z.logRead i ≠0
  have ht:= Meadow.furlough Y (Z:=X') (H:=X') (fun _=>rfl) hv.low
  have he i : ∀ᶠ j in atTop,¬ P j i:= by
    by_cases hi:z.logRead i=0; · filter_upwards with j using (fun h=> h.2 hi)
    let s:= pennant H i
    have hu: Coast.kept F sizes H Ω k s.2:= by contrapose! hi; exact (Coast.posts_id F sizes H (Coast.kept F sizes H Ω k) i).trans (if_neg hi)
    have hZ : opus H (Divides.selfA H) O γ s.2 ≠ 0:= by
      intro h; apply hi; change Rim c • (_ ∘ s.1.view) = _; rw [Divides.bySong,if_pos hu,h]; ext; simp
    filter_upwards [ambitious F sizes H Z Ω h k s.2 hu hZ] with j hj; exact fun h=> h.1 ((Cabinet.earns ..).2 hj)
  filter_upwards [Meadow.limits (P:=X') (h:=fun _=>z) Y P 0 ht he hd] with k hk
  let T₀ i:= if i ∈ (B).board L k then (0:Config G c→ℝ) else z.logRead i
  have ht i: (if P k i then z.logRead i else 0)=T₀ i:=by by_cases h:i∈ (B).board L k; · simp [P,T₀,h]
                                                         by_cases hh:z.logRead i=0 <;> simp [P,T₀,h,hh]
  obtain ⟨f,h₁,h₂⟩:=hk; refine ⟨f,h₂,fun i=>?_⟩
  change (Y).Regular _ (T₀ i) ∧ (Y).supBounds _ _ (T₀ i) _; rw [← ht]; split; exact ⟨hv.low.smooth i,by convert h₁ i; rw [if_pos (by assumption : P k i)]⟩; exact ⟨CouplingShape.reg_const _,by convert h₁ i; rw [if_neg (by assumption : ¬P k i)]⟩

omit F h sizes H hv hd in
lemma budgetS {c:Side} {ι : Type} {u v : ι → Config G c→ℝ} {X : ι→RegularAddress c} {p:BudgetPoint} {b a : ℝ}
    (h : Meadow.Budget p X u b) (he : Meadow.Budget p X v a) : Meadow.Budget p X (u+v) (b+a) := by
  obtain ⟨t,ht,hV⟩:= h; obtain ⟨z,hz,hZ⟩:=he
  refine ⟨t+z,fun i=>?_,fun i=>?_⟩
  · convert budget_plus (ht i) (hz i) using 2 with x; simp only [Pi.add_apply, add_mul]; split<;> simp
  change p.Regular _ (u i+v i) ∧ p.supBounds _ _ (u i+v i) _; rw [show u i+v i=u i-((-1:ℝ) • v i) by simp]
  have hp:= CouplingShape.reg_scale (-1) (hZ i|>.1); refine ⟨CouplingShape.reg_sub (hV i|>.1) hp,CouplingShape.sup_sub (hV i|>.1) hp (hV i|>.2) ?_⟩
  have hh:= CouplingShape.sup_scale (-1) (hZ i|>.2); rwa [abs_neg,abs_one,one_mul] at hh

lemma sells : ∀ᶠ j in atTop,
    Collection.Local (Y') Y (Cabinet.leftward (B) O γ (High.countOrder k) j) (v+(costE k R.beta +δ)) (Coin.wage F m) := by
  filter_upwards [too_far F sizes H Z Ω h hv δ hd] with j hj
  let S₀:= Cabinet.leftward (B) O γ (High.countOrder k) j
  have hK : (Plev.fromPost F sizes R H (fun z=>z∉ Cabinet.catalogue (B) L j) γ)=S₀:= by
    have he (X Yx : Collection.Source G c) (h:X.logRead=Yx.logRead) (hp:X.hardRead=Yx.hardRead) : X=Yx:=by cases X; cases Yx; congr
    refine he _ _ (funext fun i=>?_) rfl
    rw [Coast.posts_id]; by_cases hF:i∈(B).board L j
    · simp only [(B).earns i|>.mp hF, not_true_eq_false, ↓reduceIte]; unfold S₀ Cabinet.leftward; simp only [hF, ↓reduceIte]
    simp only [mt ((B).earns i|>.mpr) hF, not_false_eq_true, ↓reduceIte]; unfold S₀ Cabinet.leftward; simp only [hF, ↓reduceIte]
  let u i:= if i∈ (B).board L j then 0 else (Coast.weeded F sizes H Ω k|>.logRead i)
  let z i:= if i∈ (B).board L j then 0 else (Coast.kept_out F sizes H Ω k|>.logRead i)
  have hz : S₀.logRead= (Coast.inherited F sizes H Ω|>.logRead) + (u+z):= by
    funext i; unfold S₀ u z Cabinet.leftward; simp only [Pi.add_apply]; split
    next hx=> rw [aperture F sizes H Z Ω h j i hx, add_zero,add_zero]
    next _ => rw [Coast.sumId F sizes H Ω k]; abel
  have hp : Meadow.Budget Y (Y').reg S₀.logRead (v+(costE k R.beta +δ)) := by
    rw [hz]; refine budgetS hv.bills (budgetS (Meadow.emptyFree _ Y hv.tails u (fun i=>?_)) hj)
    unfold u; split <;> simp
  have h₀ := Coast.portioning F sizes H (fun z=>z∉ Cabinet.catalogue (B) L j) hv.allE; rw [hK] at h₀
  obtain ⟨g,hg,hG⟩:=hp; exact ⟨h₀.smooth,h₀.family,h₀.transforms,⟨g,fun i=> (hG i).2,hg⟩, h₀.expensive⟩
end Ports
end YM.RGComparison01

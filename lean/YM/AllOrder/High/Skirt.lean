import YM.AllOrder.High.Canon
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Loft

/-!
# Keep wages on the untouched remainders

Any Crew family. This finishes the analytic high-density step into the
computation up to error *after classification*, before comparing with PT
models of the low. Supply old-path terminal high bounds separate from E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {k j m π : ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
local notation "B" => radiusB p
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)

lemma chan_budget {ι:Type} (A : ι→RegularAddress c) (P:BudgetPoint) (f g : ι→ Config G c→ℝ)
    (hp : Meadow.Budget P A f U) (hv:Meadow.Budget P A g V): Meadow.Budget P A (f+g) (U+V):= by
  obtain ⟨k,h',hv'⟩:=hv; obtain ⟨c',hc,hF⟩:=hp; refine ⟨c'+k,fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (hc i) (h' i) using 2 with x; dsimp only [Pi.add_apply]; split <;> ring
  have hh:(f+g) i=f i-((-1:ℝ) • g i):= by simp
  have hp:= CouplingShape.reg_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1); rw [hh]; refine ⟨hp,?_⟩
  have hb:= CouplingShape.sup_scale (-1) (hv' i).2; rw [abs_neg,abs_one,one_mul] at hb; exact CouplingShape.sup_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1) (hF i).2 hb

open Height
variable (α : H.fragrances → Prop) (P:BudgetPoint) (χ : Chi)

def unplugged (x:Magazine H) : Prop := x.elim α (fun i=> B < Meadow.arc T.down i)
def journey (γ:ℝ) (i:Magazine H) : Config G c→ℝ := if unplugged α i then opus H Θ χ γ i else 0

lemma hit_trust {r s z w v a a' b d d' θ : ℝ}
    (N:Captain H j z w v a r s b d d' m χ) (he : Ac.Hit (Captain.reachability (H:=H)) (radiusB p) (fun i=> if α i then N.markΦ i k else 0) a' θ)
    (hp:P.threshold=Pressure.temp p) (ht:P.B=radiusB p) (h:P.order≤j) (hk:P.power≤k) (hf:preExponent P≤a'):
    Meadow.Budget P (Beam.dashboard H) (fun i=> if α i then Song.sequence H Θ χ i else 0) θ:= by
  let Y i:= if α i then N.markΦ i k else 0; let D i:= if α i then Song.sequence H Θ χ i else 0
  have h i : P.Regular (Beam.dashboard H i).support (D i) ∧ P.supBounds (Beam.dashboard H i).site (Beam.dashboard H i).support (D i) (Y i):=by
    unfold D Y; split
    · have hk' := N.gloryBudget i P hp h; rw [Beam.see]; have hz:= CouplingShape.sup_scale (-1) (hk'.2.2 k hk _ (show _ from (Beam.see H i) ▸ (Beam.dashboard H i).anchor)); rw [abs_neg,abs_one,one_mul] at hz; unfold Song.sequence; rw [flip_noop]; exact ⟨CouplingShape.reg_scale _ hk'.2.1,hz⟩
    exact ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
  refine ⟨Y,fun x=> budget_mono (he x) (fun i=>?_) (fun i=>?_),h⟩
  · split; next =>exact mul_nonneg (h _|>.2.1) (Real.exp_nonneg _)
    exact le_rfl
  split
  next hi => dsimp only at *; rw [Beam.see,ht] ; rw [if_pos (show x∈ Captain.reachability i from hi ▸ (show _ ∈ perf H i from Beam.see H i ▸ (Beam.dashboard H i).anchor))]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg _))) (h i|>.2.1)
  exact (he x).1 i

lemma cruise (γ:ℝ) {y b σ Λ C : ℝ} (hH: Meadow.Budget P (Beam.dashboard H) (fun i=> if α i then Song.sequence H Θ χ i else 0) y)
    (ht:P.B=radiusB p) (h:T.down.Bounds T.low σ C Λ) (hP:WilsonStartup.Decent T.low P) (hs : preExponent P/P.B≤ σ/4)
    (hb : Real.exp (-(σ/4)*P.B)*Song.octaveNeed G P T.low σ C Λ R.beta γ ≤ b) :
    Meadow.Budget P (Beam.marquee H P).reg (choir (journey α χ γ) ∘ pennant H) (turnFee P*(y+b)):= by
  obtain ⟨f,hF,hV⟩:= hH; obtain ⟨k',hK,hP⟩:= Meadow.lent (c:=c) P _ _ _ γ h hP hs
  have hz z:0≤k' z:=(hP z).2.1; let z i:= if B < Meadow.arc T.down i then k' i else 0
  let K: Magazine H→ℝ:= Sum.elim f z; have hv i : 0 ≤ z i:= by unfold z; split; exact hz _; exact le_rfl
  apply Meadow.soared P
  refine ⟨K,fun x=>Cost.sum (hF x) (show SumBudget _ b from ?_),?_⟩
  · rw [ht] at hb
    have ht:= Meadow.arch_tail (strings T.down P) P (Meadow.arc T.down (c:=c)) hK (k:=B) (by have h:= h.width; positivity) hz x
    refine budget_loosen (budget_mono ht (fun i=> ?_) (fun i=> ?_)) hb
    · split; next h=> exact mul_nonneg (hv _) (Real.exp_nonneg _)
      exact le_rfl
    ·
      by_cases he: B< Meadow.arc T.down i
      · dsimp only [Beam.contents,K]; simp_rw [Sum.elim_inr,z,if_pos he,if_pos he.le]; exact le_rfl
      dsimp only [Beam.contents,K,Sum.elim]; unfold z; rw [if_neg he]; split
      next h=> rw [zero_mul]; split_ifs <;> first | exact mul_nonneg (hz _) (Real.exp_nonneg _)| simp
      exact le_rfl
  intro i; rcases i with i|i
  · exact hV i
  unfold journey; split; next h=> rw [show K (.inr i)=_ from (if_pos h : z i=k' i)]; exact hP i
  next h=> rw [show K (.inr i)=_ from (if_neg h : z i=0)]; exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=P) (X:=(strings T.down P i).support) (o:=(strings T.down P i).site) 0)⟩

-- occupancy can be any k, but unused terms in short convolution eventually pay after fixing Beta & torus. keep caps identical.
lemma finite_bonus {t u b:ℝ} (γ:ℝ) (hf:Collection.Local (posting P H) P (plusone H Θ χ γ) t u)
    (F : ℕ→ Finset H.fragrances) (he : ∀ i, ¬α i→ (∃ U,stream H χ U i≠0) →∀ᶠ k in atTop, i∈F k)
    (hg : Meadow.Budget P (Beam.marquee H P).reg (choir (journey α χ γ) ∘ pennant H) V) (hb:0 < b):
    ∀ᶠ k in atTop, Meadow.Budget P (Beam.marquee H P).reg (leftover (F k) χ k γ).logRead (V+b):= by
  let f:=(plusone H Θ χ γ).logRead; let h := choir (journey α χ γ) ∘ pennant H; let w (k:ℕ) i:= ¬ unplugged α (pennant H i).2 ∧ i ∉ foliage (F k) k ∧ f i ≠ 0
  let u (k:ℕ) i:= if w k i then f i else 0
  have hr (i:ℕ) : (∃ U, (plusone H Θ χ γ).logRead i U≠0) ↔ f i≠ 0:= (Function.ne_iff ..).symm -- type
  have hs i: ∀ᶠ k in atTop, ¬w k i := by
    by_cases hp:f i=0; · exact Eventually.of_forall fun k hw=> hw.2.2 hp
    by_cases h: unplugged α (pennant H i).2; · exact Eventually.of_forall fun k hw=> hw.1 h
    let v:= pennant H i; let y:= v.2; change ¬ unplugged α y at h
    suffices hy: ∀ᶠ k in atTop,y∈blossom (F k) k from hy.mono fun k hy hw=> hw.2.1 ((leaves ..).2 hy)
    cases hz:y with
    | inl z =>
      rw [hz] at h; obtain ⟨U,hp⟩:=(hr i).2 hp; have hp':stream H χ (v.1.view U) z≠0:= by
        change Song.Rim c * opus H Θ χ γ y _≠0 at hp; rw [hz] at hp; change Song.Rim c * (-1*stream H χ (v.1.view U) _ ) ≠ 0 at hp; rw [flip_noop] at hp
        contrapose! hp; rw [hp]; ring
      exact (he z h ⟨_,hp'⟩).mono fun k hk=> inl_mem_disjSum.mpr hk
    | inr z=>
      rw [hz] at h; obtain ⟨⟨s,i⟩,hv⟩:= (Meadow.rollers _).surjective z
      have hx : Meadow.melody T.down i ≤ B:= le_of_not_gt (show ¬ B < Meadow.melody T.down i from (by rw [← Meadow.arc_receipt T.down s i,show Meadow.legs s i=z from hv]; exact h))
      exact (Meadow.burgeoning T.down B i hx).mono fun k hk=> inr_mem_disjSum.mpr (mem_map.mpr ⟨(s,i),mem_product.mpr ⟨mem_univ _,hk⟩,hv⟩)
  have hl:= Meadow.limits P w (P:=Beam.marquee H P) 0 (h:=fun s=> plusone H Θ χ γ) (Meadow.furlough P (H:=Beam.marquee H P) (fun i=> (Beam.rewrite_rule H P i).symm) hf) hs hb
  filter_upwards [hl] with k hk; obtain ⟨g,hg',hw⟩:= hk; have hf : Meadow.Budget P (Beam.marquee H P).reg (u k) b:= ⟨g,hw,fun i=> ⟨(by
    unfold u; split
    · rw [Beam.rewrite_rule]; exact hf.smooth i
    exact CouplingShape.reg_const _),by unfold u; convert hg' i using 1; split_ifs <;> rfl⟩⟩
  refine Meadow.emptyFree _ _ (chan_budget _ _ h (u k) hg hf) _ ?_; intro i
  let v:= (pennant H i); have hG: h i=(if unplugged α v.2 then f i else 0):= by
    unfold h; change Rim c • (journey α χ γ v.2 ∘ v.1.view)=_; unfold journey; split; rfl; ext; simp
  change h i+u k i=_∨ _; rw [ledger]; by_cases he:i∈foliage (F k) k; · exact Or.inr (if_pos he)
  rw [if_neg he]; by_cases hv:unplugged α v.2
  · have hg:¬w k i:=fun h=> h.1 hv; left; unfold u; rw [if_neg hg,add_zero,hG,if_pos hv]
  by_cases hl:f i=0; · exact Or.inr hl
  have hh:w k i:= ⟨hv,he,hl⟩; left; unfold u; rw [if_pos hh,hG,if_neg hv,zero_add]
end YM.AllOrder.High

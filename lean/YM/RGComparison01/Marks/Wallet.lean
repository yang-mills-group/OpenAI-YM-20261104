import YM.RGComparison01.Marks.Stage
import YM.RGComparison01.Sail
import YM.MergeProof.Wreath
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
local notation "Z" => H.faresP
local notation "bZ" => H.birth
local notation "TZ" => Tree.Forest S.ratio
/-- The full early angular sale, distinct ancestor premium tags applied
 on *this* estimate only. -/
def freight (Ψ:ℕ→Prop) (d t D:ℝ) (i:Head S):= match i with
 | Sum.inr (.inr (.inl (.inl (.inl k)))) => if Ψ k then d else t
 | _ => Sail.policyP (fun _=>1) D i *t

lemma stock_ge (h:1≤D) (he:1≤t)(hf:1≤D') : ∀ i:Head S,1 ≤ freight Ψ D t D' i:= fun i=>by
  unfold freight; split
  next k=> split; exact h; exact he
  next=> exact one_le_mul_of_one_le_of_one_le (Sail.policy_ge _ _ hf (fun _=> le_rfl) _) he

-- incorporate probability at read of Warning.
def convertP (Ω:Utopia H j v d r C' χ) (F:Head S→ℝ) (i:Head S):= F i*Ω.rad^(blaze {i}).card
lemma prob_head (Ω:Utopia H j v d r C' χ) (i:Head S): convertP Ω Ω.tag i=Ω.fare i:= by simpa only [convertP,prod_singleton] using (Ω.remixes {i}).symm
lemma polar_eq (p:Molecule S) : (blaze p).card= ∑ i∈p,(blaze ({i}:Molecule S)).card:= by
  classical
  induction p using Finset.induction_on with
  | empty=> simp [blaze]; rfl
  | insert i s hi ih=>
    rw [sum_insert hi, ← ih]
    have hu : blaze (insert i s)=blaze ({i}:Molecule S)∪ blaze s:= by ext; simp only [blaze,mem_union,mem_toRight,mem_insert,mem_singleton]
    rw [hu,Finset.card_union_of_disjoint]; apply Finset.disjoint_left.mpr; intro z ht hz
    simp only [blaze, mem_toRight, mem_singleton] at ht hz; exact hi (ht ▸ hz)
lemma snow (F:Head S→ℝ) (p:Molecule S): (∏ i∈ p,convertP Ω F i)= (∏ i∈p,F i)*Ω.rad^(blaze p).card:= by
  simp_rw [convertP,Finset.prod_mul_distrib, polar_eq p,← Finset.prod_pow_eq_pow_sum] -- check

lemma crest_levy (Ω:Utopia H j v d r C' χ)(h: Worthy Ω (fun _=>1) D) (_ht: 1 ≤ D)(hx:1 ≤ grow G L s):
    Ac.Hit H.supportP (radiusB s)
      (tariff (fun i=> policyP (fun _=>1) D i * Ω.fare i) (Mixed.lengths S Z (ConnectedActivityE6.lengths T R)) (Mixed.stamp S Z) Q.ε)
      (H.faresP).head (H.faresP).rootHit:= by
  let X:= Q.costs L μ R.beta s C'; let t := grow G L s
  let F (i:Head S) := policyP (fun _=>1) D i * Ω.fare i; let ζ i:= crestP c f (fun _=>1) D i*Ω.flair i
  have he : ∀ i:ConnectedActivityE6.Alphabet c f,1 ≤ t^Silica.horn i:=fun i=>one_le_pow₀ hx
  have hz : Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s)) ζ (Sum.elim (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L s):= by
    apply Silica.Clutch.Market.salesM (fun i=> t^Silica.horn i) he
    simp_rw [ζ, show ∀ i, t^Silica.horn i*(crestP c f (fun _=>1) D i * Ω.flair i)= (crestP c f (fun _=>1) D i * t ^ Silica.horn i)*Ω.flair i from fun i=> by ring]; exact h
  have hh : Ready H.supportP (radiusB s) (tariff F (Mixed.lengths S Z (ConnectedActivityE6.lengths T R)) (Mixed.stamp S Z) Q.ε) (Q.exp+2*Q.ε) X.rootHit Q.δ (1/2) := by
    rw [show F = Mixed.costs S Q.halo (radiusB s) (steamP S X) ζ from ?_]
    · exact Mixed.ready_vertices S Q.halo (radiusB s) X bZ ζ (ConnectedActivityE6.lengths T R) (steamP S X) Ω.lives ⟨Ω.accrues.packetBound,hz.nonneg,Ω.accrues.extra,hz.hit⟩
    funext i; rcases i with i|i
    · change 1*_=_; rw [one_mul]; rfl
    rfl
  exact hh.2.2.2.2.2

abbrev stairs (_H : Cash W s μ L Q o C T R):= Mixed.lengths S _H.faresP (ConnectedActivityE6.lengths T R)
abbrev tolling (_H : Cash W s μ L Q o C T R): Head S→ℝ:= Mixed.stamp S _H.faresP
-- fare of an unmarked head when no chosen leaf. d carries rough vac error.
def liftedPay (Ω:Utopia H j v d r C' χ) (Ψ:ℕ→Prop) (x:ℕ→ℝ) (e D t D':ℝ) (i:Head S):= freight Ψ D t D' i * convertP Ω (maskRaise Ω Ψ x e) i
lemma pay_ge (Ω:Utopia H j v d r C' χ) (hd:1≤D)(ht:1 ≤ t)(hx:1≤D')(hf:Casing R x Ψ) (he:0 ≤ e) : ∀ i,0 ≤ liftedPay Ω Ψ x e D t D' i:= fun i=> mul_nonneg (zero_le_one.trans (stock_ge hd ht hx i)) (mul_nonneg (raises _ he hf.nonneg _) (pow_nonneg Ω.awake _))
lemma crownPay (Ω:Utopia H j v d r C' χ) (hz : Worthy Ω (fun _=>1) D') (hQ:1 ≤ grow G L s)
    (hd:1≤D)(ht:1≤t)(hx:1≤D')(hf:Casing R x Ψ)(he:0≤ e)
    (hY:Sales (radiusB s) Q.relative Q.ε (Raw.regularFoot S.ratio Q.halo (radiusB s) R) (fun i=> x i) (Raw.regularExtra R) δ):
    Ac.Hit H.supportP (radiusB s) (tariff (liftedPay Ω Ψ x e D t D') (stairs H) (tolling H) Q.ε) H.faresP.head
      ((t*r^j)*(H.faresP).rootHit + (D*e)*δ):= by
  let l:ℕ→Head S:= fun i=> (Wing.logKey i).badge S
  let Y : ℕ ↪ Head S := ⟨l,fun i j h=> by simpa only [l,Wing.badge,Sum.inr.injEq,Sum.inl.injEq] using h⟩
  let b:=Reserves.tariff x (fun i=> (Raw.regularExtra R i:ℝ)) 0 Q.ε; let g:= Function.extend Y b 0
  let B:=H.faresP.head; let X:=radiusB s
  let P:=fun i:Head S=>convertP Ω (maskRaise Ω Ψ x e) i; let f:=fun i=>freight Ψ D t D' i * P i
  have hv':0 ≤ r:= zero_le_one.trans Ω.active
  have hw : Ac.Hit H.supportP X g B δ := by
    intro i; refine Progress.DirectedRecipe.transfer_budget Y ?_ ?_ (hY.hit i)
    · intro j; unfold g; rw [Y.injective.extend_apply]; rfl
    intro j hj; unfold g; rw [Function.extend_apply' _ _ _ hj]; change (if _ then 0*_ else (0:ℝ)) = _; split <;> simp
  have he':= crest_levy Ω hz hx hQ; let v:=t*r^j; have h₀:0≤v:=mul_nonneg (zero_le_one.trans ht) (pow_nonneg hv' _)
  let s':=tariff (fun i=> policyP (fun _=>1) D' i * Ω.fare i) (stairs H) (tolling H) Q.ε
  have h₁ i:0 ≤ s' i:= mul_nonneg (mul_nonneg (zero_le_one.trans (policy_ge _ _ hx (fun _=> le_rfl) _)) (Ω.fares _)) (Real.exp_nonneg _)
  intro i; have hC := budget_plus (budget_scale h₀ (he' i)) (budget_scale (mul_nonneg (zero_le_one.trans hd) he) (hw i))
  refine budget_mono hC ?_ ?_
  · intro j; split; exact mul_nonneg (mul_nonneg (pay_ge Ω hd ht hx hf he _) (Real.exp_nonneg _)) (Real.exp_nonneg _); exact le_rfl
  intro j'; split
  next hu =>
    refine le_trans (b:=Reserves.tariff f (stairs H) (tolling H) Q.ε j'*Real.exp (B*coverNumber X (H.supportP j'))) le_rfl ?_
    change _ ≤ v*(s' j'*_)+(D*e)*(g j'*_)
    apply le_trans (mul_le_mul_of_nonneg_right (show Reserves.tariff f (stairs H) (tolling H) Q.ε j' ≤ v*s' j' + D*e*g j' from ?_) (Real.exp_nonneg _)) (le_of_eq (by ring))
    have hc j' : 0 ≤ D*e*g j' := by
      unfold g; by_cases h:j' ∈ Set.range Y
      · obtain ⟨u,rfl⟩:=h; rw [Y.injective.extend_apply]; exact mul_nonneg (mul_nonneg (zero_le_one.trans hd) he) (mul_nonneg (hY.nonneg _) (Real.exp_pos _).le)
      rw [extend_apply' _ _ _ h,show (0:Head S→ℝ) j'=0 from rfl,mul_zero]
    have hP' (i) (hi : freight Ψ D t D' i= Sail.policyP (fun _=>1) D' i * t) (hq:maskRaise Ω Ψ x e i= Ω.tag i*r^j): Reserves.tariff f (stairs H) (tolling H) Q.ε i ≤ v*s' i+D*e*g i:= by
      apply le_trans _ (le_add_of_nonneg_right (hc _)); apply le_of_eq; unfold f P s' tariff v; dsimp only; rw [hi,← prob_head]; unfold convertP; rw [hq]; ring
    by_cases hn : ∃ n, Ψ n ∧ j'=Y n
    · obtain ⟨n,h,rfl⟩:=hn
      apply le_trans _ (le_add_of_nonneg_left (mul_nonneg h₀ (h₁ _)))
      unfold g; rw [Y.injective.extend_apply]; apply le_of_eq
      have he' : blaze {Y n}=∅:= by ext; simp only [blaze,mem_toRight,notMem_empty,iff_false,mem_singleton]; simp [Y,l,Wing.badge]
      unfold f P b tariff convertP; dsimp only; rw [he',show freight Ψ D t D' (Y n)=D from if_pos h,show maskRaise Ω Ψ x e (Y n)= e*x n from if_pos h, show tolling H (Y n)=0 from (by unfold tolling Mixed.stamp; simp [Y,l,Wing.badge,Mixed.shares])]; change D*(e*x n*Ω.rad^(∅: Finset (WarningAt _ _)).card)*Real.exp (2*Q.ε*(Raw.regularExtra R n)+0) = D*e*(_*Real.exp (2*Q.ε*(Raw.regularExtra R n)+ (0:ℝ))); simp; ring
    apply hP'
    · unfold freight; split
      next k=> rw [if_neg (fun hv=>hn ⟨k,hv,rfl⟩),show policyP (S:=S) _ _ _=1 from rfl,one_mul]
      next=> rfl
    unfold maskRaise; split
    next k=> exact if_neg (fun hv=>hn ⟨k,hv,rfl⟩)
    next=> rfl
  next => rw [mul_zero,mul_zero,add_zero]
end YM.RGComparison01.Pledge

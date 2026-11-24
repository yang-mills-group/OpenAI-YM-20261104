import YM.LocalLTE.Tier.Brim
import YM.LocalLTE.Tile.Allot
/-! All Birth E. Component prices charged EACH actual E input address.
This can be applied, for example, to independently stored signed remainder in E
so all its reads (however tiny) stay tagged through entire step. Exposes principal
V9 curvature estimate (1/L) isolated. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Beam
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    {H : Cash W s μ L Q o α T I} {p : BudgetPoint} {J : Cash W s μ L Q o α T R} {χ : Chi}
local notation "η"=> Meadow.intern H
lemma droplets (F':ℕ→ℝ) i : rocket H F' (icon H i)=F' i:= by
  unfold rocket; simp [icon,surge,once,Brim.head,Opacity.key]; rfl
-- ok too-large plate is T tired. If need include negligibles.
def nearbound (z:H.fragrances):= coverNumber (radiusB s) (H.bookFoot (.inr z))≤radiusB s
lemma oldWave (z:H.fragrances) (x:Config G c) (he : ¬tiredN H 3 z) (hv:stream H χ x z ≠ 0) (hp:ancestry z) : z∈ Set.range (Brim.icon H)∧ nearbound z := by
  obtain ⟨hA,h⟩:= aging hv he; obtain ⟨i,k,hk⟩:= hp; have ht:= lt_of_not_ge (not_or.mp he|>.1)
  have hC:1≤ acmeN H 3 z := (single_le_sum (f:=Sum.elim (fun _:Stores S =>0) (Silica.hornN 3)) (fun i _=> Nat.zero_le _) hk|>.trans (single_le_sum (f:=fun i=>pinsN 3 S (z.2 i).val) (fun i _=> Nat.zero_le _) (mem_univ i)))
  have hℓ: breadth H z ≤1 := by unfold degreeN at ht; omega
  have ha := hA i
  have hN := lantern z (fun i=> (hA i).nonempty) hℓ i hk
  refine ⟨⟨k,hN.symm⟩,?_⟩
  have hh:= (shaped (H:=H) (z.2 i).val ha.connects).trans ha.pays
  have hr : H.bookFoot (.inr z)=H.unionP (z.2 i).val:= by
    generalize_proofs at *
    suffices hk : ∀ j,H.bookFoot (.inr z)=H.unionP (z.2 j).val from hk i
    rw [hN]; exact fun i=> (sites_icon ..).trans (concern ..).symm
  unfold nearbound; rw [hr]; exact_mod_cast hh

-- signal tag weighting. Don't assume Prices for comparison buys. 
set_option maxHeartbeats 500000 in
lemma crest (F':ℕ→ℝ)(hM:∀ i,1≤ F' i) (N : Captain H j C' d v Y A b r B q k χ) {a'' u h f' :ℝ}{τ ε : Chi}{D: JointLoad.Heir.Record}
    (hX: Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> if tiredN H 3 z then rocket H F' z*N.markΦ z n else 0) a u)
    (hK:Brim.Hauses F' H D τ ε χ γ p a'' h f') (hb:p.B=radiusB s) (hs:p.supportExponent+3 ≤ a'') (ht:p.threshold=Pressure.temp s)(hp:p.order≤j)(hq:p.power≤n):
    ∃ f₁ : H.fragrances → ℝ, (∀ i:H.fragrances, Height.ancestry i → p.Regular (dashboard H i).support (sequence H η χ i)∧
          p.supBounds (dashboard H i).site (dashboard H i).support (sequence H η χ i) (f₁ i)) ∧
     let X₀ (z:H.fragrances):=if Height.ancestry z then rocket H F' z * f₁ z else 0
     early p (Beam.dashboard H) (fun z=> if z∈Set.range (Brim.icon H)∧ nearbound z then X₀ z else 0) (h+f')∧
     Ac.Hit (Captain.reachability (H:=H)) p.B (fun z=> if z∈Set.range (Brim.icon H)∧ nearbound z then 0 else X₀ z) a u := by
  obtain ⟨⟨f₀,hh,h'⟩,a',hz,hY⟩:= hK
  let T i:= N.markΦ i n
  have ht' i:p.Regular (dashboard H i).support (sequence H η χ i) ∧ p.supBounds (dashboard H i).site (dashboard H i).support (sequence H η χ i) (T i) := by
    have hk:= N.gloryBudget i p ht hp; rw [see];
    simp only [Song.sequence, Meadow.coincides H] -- syntax edit
    refine ⟨CouplingShape.reg_scale _ hk.2.1,?_⟩
    have hh:= CouplingShape.sup_scale (-1) (hk.2.2 n hq (dashboard H i).site (show (dashboard H i).site ∈ perf H i from (Beam.see H i) ▸ (dashboard H i).anchor)); rw [abs_neg,abs_one,one_mul] at hh; exact hh
  have hs' i (he : nearbound (icon H i)) : p.supBounds (plate H i).site (plate H i).support (sequence H η χ (icon H i)) (f₀ i+a' i):= by
    rw [show sequence H η χ (icon H i)=announced H D τ ε γ i-glyph H D τ ε χ γ i from (by ext V; change (-1:ℝ)* stream H χ V ((η).furrow _) = _- (stream H χ V _+_); rw [mimics _ _ rfl]; ring)]; unfold nearbound at he
    rw [sites_icon,← hb] at he; exact CouplingShape.sup_sub (hh i).1 (hY i).1 (hh i).2 ((hY i).2 he)
  let V (i:H.fragrances):Prop:= i∈Set.range (Brim.icon H) ∧ nearbound i
  let a₀:= extend (Brim.icon H) (fun i=> f₀ i+a' i) 0
  let q₀ z:= if V z then a₀ z else if tiredN H 3 z then T z else 0
  have ht i (hi: Height.ancestry i) : p.supBounds (dashboard H i).site (dashboard H i).support (sequence H η χ i) (q₀ i) := by
    by_cases he: V i
    · obtain ⟨⟨j,rfl⟩,hz⟩:= (show _∈Set.range _ ∧_ from he)
      unfold q₀ a₀; rw [if_pos he,(icon_inj H).extend_apply,impact]; exact hs' _ hz
    unfold q₀; rw [if_neg he]; by_cases hk:tiredN H 3 i
    · rw [if_pos hk]; exact (ht' i).2
    rw [if_neg hk]
    rw [show sequence H η χ i=(0:Config G c→ℝ) from ?_]; simpa only [abs_zero] using! (CouplingShape.sup_const (p:=p) (o:=(dashboard H i).site) (X:=(dashboard H i).support) (G:=G) 0)
    ext x
    change -1 * stream H χ x ((η).furrow i)=0
    rw [-- eta
       show (η).furrow i=i from Meadow.coincides .., show stream H χ x i=0 from not_ne_iff.mp fun h=>he (oldWave i x hk h hi),mul_zero]
  refine ⟨q₀, fun i hi=> ⟨(ht' i).1, ht i hi⟩,fun s=>?_, ?_⟩
  · apply Beam.wallet (⟨_,icon_inj H⟩:ℕ↪ H.fragrances) (budget_mono (budget_plus (h' s) (hz s)) ?_ ?_) ?_
    · intro i; dsimp only [Function.Embedding.coeFn_mk]; split_ifs
      next _ hh he => exact mul_nonneg (mul_nonneg (rocket_pos H F' hM _) (ht _ he).1) (Real.exp_pos _).le
      all_goals simp
    · intro i; dsimp only [Function.Embedding.coeFn_mk, Pi.add_apply]
      by_cases he: (dashboard H (icon H i)).site=s ∧ V (icon H i) ∧ ancestry (icon H i)
      · obtain ⟨he,hv,hΓ⟩:=he; rw [if_pos he, if_pos hv,if_pos hΓ]
        have hg:= ht _ hΓ
        have hE : p.supportExponent+3 ≤ a'':= hs; change preExponent p ≤ a'' at hE
        apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg _))) (mul_nonneg (rocket_pos H F' hM _) hg.1)); apply le_of_eq
        rw [impact] at he ⊢; rw [if_pos he,if_pos he]; unfold q₀ a₀; rw [if_pos hv,(icon_inj H).extend_apply,droplets]; ring
      have he':= (budget_plus (h' s) (hz s)).1 i
      apply le_trans ?_ he'; unfold V at he
      split_ifs <;> first| rfl| simp only [zero_mul,le_refl]| (exfalso; exact he ⟨by assumption, And.intro (by assumption) (by assumption)⟩)
    intro z he; split; next hA=>
      have hi:z∉Set.range (Brim.icon H):= he
      simp [hi]
    rfl
  intro s'; rw [hb]; refine budget_mono (hX s') (fun i=> ?_) (fun i=>?_)
  · dsimp only
    split
    next hx =>
      split
      next => simp
      next =>
        split
        next he => exact mul_nonneg (mul_nonneg (rocket_pos H F' hM _) (ht _ he).1) (Real.exp_pos _).le
        simp
    exact le_rfl
  dsimp only; split
  next hi =>
    have hz := (hX s').1 i; dsimp only at hz; rw [if_pos hi] at hz
    by_cases hu: V i
    · rw [if_pos (show _ ∧ _ from hu),zero_mul]
      exact hz
    rw [if_neg (show ¬ (_ ∧ _) from hu)]
    split
    next hp =>
      unfold q₀; rw [if_neg hu]; split
      next ht=> exact le_rfl
      simp
    rw [zero_mul]; exact hz
  exact le_rfl
end YM.PhysicalNext.Repeat.Beam

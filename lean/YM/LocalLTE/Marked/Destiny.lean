import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Widow
import YM.LocalLTE.Marked.Force
import YM.LocalLTE.Tier.Vine
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Price
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Use

/-! # Earn sharp HIGH-arity unforced activities at the actual early budget

Two forest bounds simultaneously. Higher arity means every vertex,
 occurrence count, not just each cluster slot. Includes seed gain
 via stamp. Movement through F-average uses uniform bound not
 requiring that a Rain patch be analytic outside mask convention.
 -/
/-! Local LTE reiteration of the bookkeeping adapted from
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Widow`.
New increment n₀ Arbitrary on non-inherited beyond-bulk grades.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}
section first
variable (N : Captain H j C' d v Y A b r B q k χ) {D : ℝ} (hd : 1 ≤ D)
variable (hhd : 1 ≤ grow G L s) {F':ℕ→ℝ}(hR:∀ i,1≤F' i) (h : HeavyT F' ℓ N.conduit)
include hR hhd N h
variable {ι:Type}[Fintype ι](M:ι→Lotus.Leaf R) (rA:ι→ℝ)(hA:∀ i,0 ≤ rA i)
open YM.Merge
set_option quotPrecheck false
local notation "κU"=> N.conduit
local notation "τ"=> grow G L s
local notation "sx"=> radiusB s
local notation "t₀"=> (Height.mcount (S:=S) (G:=G) (L:=L) (s:=s) M rA F' ℓ)
variable (hF:Daisy.foam Q L)(ht:R.p.B ≤2*(radiusB s))
    (hr: (∑ i,mcount (S:=S) (G:=G) (L:=L) (s:=s) M rA F' ℓ i*R.p.mass (M i).crest (M i).weight) ≤ Q.goal L s)
-- no notation in variable binders replace! `G` name arguments maybe unresolved syntax


-- The expenses along stoicho. Fill debt.*
local notation "E'"=> shortfall Q L μ s k
local notation "Sw"=> Daisy.swing Q L μ R.beta s C'
-- κU etc imported (check)
def pier (u:H.ThinP) := 2^j*(B*bought N M rA u.val)
def slideΖ (z:H.fragrances) := clusters H.seam (pier N M rA) z.snd
def markU (z:H.fragrances) (n:ℕ) := (shiftG s*(1+coverNumber (radiusB s) (reachability (H:=H) z)))^(n*j)* slideΖ N M rA z
def allotQ (k j:ℕ)(B' s:ℝ) (Q:ConnectedActivityE6.Target G P)(L:Side)(μ:ℝ):ℝ:= 2^j*B'*shortfall Q L μ s k+shortfall Q L μ s k
omit h hhd hR
include hA
lemma owed (u:H.ThinP): 0 ≤ pier N M rA u:=by unfold pier; exact mul_nonneg (pow_nonneg zero_le_two _) (mul_nonneg N.balance (awarded N M rA hA _))
omit hA
lemma wieldQ (z:H.fragrances): clusters H.seam (fun u:H.ThinP=> surge F' S u.val*strongerN ℓ H u.val*pier N M rA u) z.snd= beaconN H ℓ z*(rocket H F' z*slideΖ N M rA z):= by
  unfold slideΖ clusters strongerN gust
  unfold beaconN degreeN acmeN breadth depth overlap
  simp only [rocket,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Nat.cast_sum,pow_add,mul_sum,Real.exp_sum]
  ring
include h hhd hR hA hF ht hr
variable (hQ:(Daisy.swing Q L μ R.beta s C').Buy S.patch.L Q.halo (radiusB s))
    (hs : degreePrice (radiusB s) (grow G L s*(Daisy.swing Q L μ R.beta s C').rootHit) Q.δ ≤1/2)
include hQ hs
local notation "H'"=> allotQ k j B s Q L μ
lemma qlocal4a_stableQ (i a : ℝ) (hi : 0 < i) (hT : a+i+i ≤ Q.exp) (hv : 0<shortfall Q L μ s k)
    (hp : degreePrice (radiusB s) (H') i ≤ 1/2) :
    Ready H.smallAt (radiusB s) (fun p:H.ThinP=> surge F' S p.val *strongerN ℓ H p.val*pier N M rA p) (a+i) (H') i (1/2) := by
  let m (u:Molecule S):=surge F' S u*strongerN ℓ H u
  let f z:=m z*Height.bought N M rA z
  have hr : Ac.Hit H.unionP (radiusB s) f Q.exp _ := qlocal4a_strikesQ N hhd hR h M rA hA hF ht hr hQ hs
  have hD:0<grow G L s:=zero_lt_one.trans_le hhd; have hh:=N.balance
  refine ⟨by unfold allotQ; positivity,hi,hp,by norm_num,fun p=>mul_nonneg (by
    have he₀:= surge_one (S:=S) hR p.val; unfold strongerN gust; positivity) (owed N M rA hA p),fun x=>?_⟩
  have hy:= budget_scale (show 0≤(2:ℝ)^j*B by positivity) (budget_pull (fun z:H.ThinP=>z.val) Subtype.val_injective (hr x))
  refine budget_loosen (budget_mono hy (fun z=>?_) (fun z=>?_)) (le_add_of_nonneg_right hv.le)
  · dsimp only; split
    next => exact mul_nonneg (mul_nonneg (by have ht := surge_one (S:=S) hR z.val; unfold strongerN gust; positivity) (owed N M rA hA _)) (Real.exp_pos _).le
    exact le_rfl
  dsimp only; split
  next hx => rw [if_pos (show x∈H.unionP z.val from hx), ← mul_assoc, show 2^j*B*f z.val=m z.val*pier N M rA z by unfold f pier; unfold m; ring]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg _))) (mul_nonneg (show 0 ≤ m z.val by have ht := surge_one (S:=S) hR z.val; unfold m strongerN gust; positivity) (owed N M rA hA _))
  exact hy.1 z
lemma extensionQ (n : ℕ) (i a:ℝ) (ha:0 ≤ a) (hi:0 < i)(hT:a+i+i ≤ Q.exp) (hv : 0<shortfall Q L μ s k)
    (hp : degreePrice (radiusB s) (H') i ≤ 1/2): Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> beaconN H ℓ z*rocket H F' z*markU N M rA z n) a
        (collars G i s j n*((H')*(1-1/2)⁻¹)) := by
  intro x
  let D:=grow G L s; have hD:0<D:=zero_lt_one.trans_le hhd
  let m (z:H.fragrances):= beaconN H ℓ z
  have hy:= log_hit_tail _ _ _ H.testS (qlocal4a_stableQ N hhd hR h M rA hA hF ht hr hQ hs i a hi hT hv hp) (add_nonneg ha hi.le) 0 x
  simp only [pow_zero,mul_one] at hy
  let v:= collars G i s j n
  have he:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hv:0 ≤ v:=by unfold v collars Reserves.polyPrice; positivity
  have hζ z:0 ≤ slideΖ N M rA z:= clusters_nonneg _ (owed N M rA hA) _
  have hz z : 0 ≤ markU N M rA z n := mul_nonneg (pow_nonneg (by positivity) _) (hζ z)
  have hm z:0 ≤ m z:= by unfold m beaconN; positivity
  have hh:= budget_scale hv hy
  refine budget_mono hh (fun z=> ?_) fun z=> ?_
  · dsimp only; split
    next => exact mul_nonneg (mul_nonneg (mul_nonneg (hm z) (rocket_pos H F' hR z)) (hz z)) (Real.exp_pos _).le
    next => exact le_rfl
  dsimp only; split
  next hx=>
      let K:= reachability (H:=H) z
      rw [if_pos (show 0 ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩),wieldQ N M rA]
      let c:ℝ:=coverNumber (radiusB s) K; have hg:0 ≤ c:= Nat.cast_nonneg _
      change m z*rocket H F' z*((shiftG s*(1+c))^(n*j)*slideΖ N M rA z)*Real.exp (a*c) ≤ v*(m z*(rocket H F' z*slideΖ N M rA z)*Real.exp ((a+i)*c))
      let d:=m z*rocket H F' z*slideΖ N M rA z; have hd:0≤d:= mul_nonneg (mul_nonneg (hm z) (rocket_pos H F' hR z)) (hζ z)
      rw [show m z*rocket H F' z*((shiftG s*(1+c))^(n*j)*slideΖ N M rA z)= ((shiftG s*(1+c))^(n*j))*d by unfold d; ring,mul_pow]; unfold v collars Reserves.polyPrice;rw [add_mul,Real.exp_add]
      apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (polynomial_cost hi hg _) (pow_nonneg he _)) hd) (Real.exp_pos _).le)
      apply le_of_eq; unfold d; ring
  next h=> exact hh.1 z
end first
end YM.PhysicalNext.Repeat.Height

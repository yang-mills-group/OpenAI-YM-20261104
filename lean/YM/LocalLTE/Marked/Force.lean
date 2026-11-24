import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Widow
import YM.LocalLTE.Marked.Debt
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
-- recover exp(ε*setPrice) jointly with all polynomial marks. Keep same ε.
private theorem extraSets {ι:Type*} [DecidableEq ι] (p:ι→Support c) (B:ℕ) (u e : ι→ℝ) (a v : ℝ) {h k : ℝ} {n:ℕ} (hu:∀ i,0≤u i) (hw:∀ i,0≤ e i)
    (ha:0≤a) (hv:0<v) (hp:Ready p B (tariff u e 0 v) (a+2*v) h k (1/2)) (x : Site c) :
    SumBudget (fun s:Finset ι=> Reserves.rooted p B u x a s*(1+setPrice p B e s)^n * Real.exp (v*setPrice p B e s))
      (Reserves.extract v n 0 0* treeYield h (1/2) 0) := by
  have he:= touch_tail p B hp x 0; simp only [Nat.zero_le, ↓reduceIte] at he
  have hh : polyPrice v n = Reserves.extract v n 0 0 := by simp [Reserves.extract]
  rw [← hh]; apply budget_mono (budget_scale (show 0≤ polyPrice v n by unfold Reserves.polyPrice; positivity) he)
  · intro i; unfold Reserves.rooted; split; next =>
      apply mul_nonneg _ (Real.exp_pos _).le; refine mul_nonneg (mul_nonneg (prod_nonneg fun i _=>hu _) (Real.exp_pos _).le) (pow_nonneg (add_nonneg zero_le_one ?_) _)
      exact Finset.sum_nonneg fun i _=> add_nonneg (Nat.cast_nonneg _) (hw i)
    rw [zero_mul,zero_mul]
  intro i; unfold Reserves.rooted; split
  next hI =>
    have hY : (∏ j∈i,u j)*currency B a (i.biUnion p) ≤ touches p B u a x i := by
      unfold touches; rw [if_pos hI]; unfold currency; simp only [Finset.prod_mul_distrib, ← Real.exp_sum,← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Ac.cover p B hI.1) ha)) (prod_nonneg fun i _=> hu _)
    rw [Reserves.set_exchange]
    let D:= setPrice p B e i; have hd:0 ≤ D:= Finset.sum_nonneg fun i _=> add_nonneg (Nat.cast_nonneg _) (hw i)
    have hx:0≤(∏ j∈i,u j)*currency B a (i.biUnion p):=mul_nonneg (prod_nonneg fun _ _=>hu _) (Real.exp_pos _).le
    apply (mul_le_mul_of_nonneg_right (mul_le_mul hY (polynomial_cost hv hd n) (show 0 ≤ (1+D)^n by positivity) (hx.trans hY)) (Real.exp_pos _).le).trans
    -- fixed syntax
    simp only [Pi.zero_apply,sum_const_zero,add_zero]; change _ ≤ _*(touches p B u a x i * Real.exp (2*v*D)); rw [show 2*v*D=v*D+v*D by ring,Real.exp_add]; apply le_of_eq; unfold D Reserves.polyPrice; ring
  next hk=> unfold touches; rw [if_neg hk,zero_mul,zero_mul,mul_zero]
variable (hhd : 1 ≤ grow G L s) {F':ℕ→ℝ}(hR:∀ i,1≤F' i) (h : HeavyT F' ℓ N.conduit)
include hR hhd N h
variable {ι:Type}[Fintype ι](M:ι→Lotus.Leaf R) (rA:ι→ℝ)(hA:∀ i,0 ≤ rA i)
open YM.Merge
set_option quotPrecheck false
local notation "κU"=> N.conduit
local notation "τ"=> grow G L s
local notation "sx"=> radiusB s
-- costs giving decorated lives. old ordinary `hip` may cost on mark badge; billed explicitly.
def mcount (F':ℕ→ℝ)(ℓ:ℕ)(i:ι):= hip F' S (Merge.Palette.sign M S i)* τ^(Sum.elim (fun _=>0) (Silica.hornN ℓ) (Merge.Palette.sign M S i))*rA i
-- H inferred.Can pass explicitly
-- within stage Candidate. lifted E label variants.
local notation "t₀"=> (Height.mcount (S:=S) (G:=G) (L:=L) (s:=s) M rA F' ℓ)
variable (hF:Daisy.foam Q L)(ht:R.p.B ≤2*(radiusB s))
    (hr: (∑ i,mcount (S:=S) (G:=G) (L:=L) (s:=s) M rA F' ℓ i*R.p.mass (M i).crest (M i).weight) ≤ Q.goal L s)
-- no notation in variable binders replace! `G` name arguments maybe unresolved syntax

def chatter (p : Head S) : ℝ := N.conduit.fare p+ Merge.Tickets.extra (Merge.Palette.sign M S) (Merge.Palette.wages M rA) p
def bought (i:Molecule S):ℝ:= if H.ticketsP 0 0 0 i then (∏ l∈i, chatter N M rA l)*(1+H.shapeW i)^k else 0
local notation "φ"=> (Height.chatter N M rA)
omit hhd h hR
include hA
lemma awarded (i:Molecule S): 0 ≤ bought N M rA i:=by
    unfold bought; split; swap; exact le_rfl
    refine mul_nonneg (prod_nonneg (fun j _=> add_nonneg (N.conduit.fares j) (?_))) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume i)) _); exact sum_nonneg (fun j _=>by split; exact mul_nonneg (hA _) (M j).profit; exact le_rfl)
include h hhd hR hA hF ht hr
local notation "Sw"=> Daisy.swing Q L μ R.beta s C'
local notation "t!"=> H.supportP
-- x0 α notation.We avoid raw Syntax
variable (hT: (Daisy.swing Q L μ R.beta s C').Buy S.patch.L Q.halo (radiusB s))
include hT
-- earner def independent geometry L post. X.costs
noncomputable def shortfall (Q:ConnectedActivityE6.Target G P) (L:Side) (μ s:ℝ)(k:ℕ):ℝ:=Reserves.extract Q.ε k 0 0 * treeYield (grow G L s*(Daisy.swing Q L μ 0 s 0).rootHit) (1/2) 0
lemma qlocal4a_strikesQ (hs : degreePrice (radiusB s) (grow G L s*(Daisy.swing Q L μ R.beta s C').rootHit) Q.δ ≤1/2): Ac.Hit H.unionP (radiusB s)
    (fun i: Molecule S=> surge F' S i* strongerN ℓ H i*Height.bought N M rA i) Q.exp (shortfall Q L μ s k):=by
  let D:=grow G L s; let X:= Daisy.swing Q L μ R.beta s C'; let E:= N.conduit; let Z:= H.supportP; let w:=Mixed.lengths S X (ConnectedActivityE6.lengths T R)
  let g (z:Head S):=hip F' S z * (D^(Sum.elim (fun _=>0) (Silica.hornN ℓ) z)*Height.chatter N M rA z); let u:=gale S X.markSeed D g
  let b:= radiusB s
  have hD:0<D:=zero_lt_one.trans_le hhd; have hg0(p:Head S):0 ≤ φ p:= add_nonneg (E.fares _) (sum_nonneg fun i _=>by split; exact mul_nonneg (hA _) (M i).profit; exact le_rfl)
  have hg p : 0≤ g p:= by
    apply mul_nonneg ?_ (mul_nonneg (pow_nonneg hD.le _) (hg0 _)); cases p with
    | inr p=> exact zero_le_one.trans (Silica.lip_one F' hR p)
    | inl=> exact zero_le_one
  have hU(i: Finset (Head S)) (p:ℝ): (∏ v∈i,gale S p (τ) g v)=surge F' S i*(D^(pinsN ℓ S) i*gust S p D i*(∏ v∈i,Height.chatter N M rA v)):= by
    simp only [g,D,gust,gale,surge,pinsN,Cash.numP,Finset.prod_mul_distrib,Finset.prod_const,Nat.cast_sum,mul_sum,Real.exp_sum,Finset.prod_pow_eq_pow_sum]; ring
  have hx0 i:0 ≤ t₀ i:=by
     refine mul_nonneg (mul_nonneg ?_ (pow_nonneg hD.le _)) (hA i)
     change 0≤ Height.hip F' S ((M i).turn.badge S); rw [← Daisy.sparkPath]; exact zero_le_one.trans (Silica.lip_one F' hR _)
  let V:= (fun i=> Merge.Tickets.extra (Merge.Palette.mark M (c:=c)) (Merge.Palette.wages M t₀) i)
  have hv : Trees.Ready Z b (tariff g w (Mixed.stamp S X) Q.ε) (Q.exp+2*Q.ε) X.rootHit Q.δ X.q := by
    let z p := Silica.lip F' p * (D ^ (Silica.hornN ℓ) p * E.flair p)
    rw [show g=Mixed.costs S Q.halo b (steamP S (Q.costs L μ R.beta s C')) (fun i=> z i+V i) from ?_]; swap
    · funext p; rcases p with p|p
      · unfold g chatter; rw [Merge.Tickets.extra,Finset.sum_eq_zero]; swap; · intro i _; exact if_neg (fun he=> by have hf:=(show .inr _ = Merge.Palette.sign M S i from Daisy.sparkPath ..).trans he; contradiction)
        unfold hip; simp; rfl
      unfold g chatter; rw [mul_add, mul_add]; refine congr_arg₂ (·+·) rfl ?_; unfold V Merge.Tickets.extra; rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk
      have hx: Merge.Palette.mark M k=p ↔ Merge.Palette.sign M S k=Sum.inr p:=by unfold Merge.Palette.mark Merge.Palette.sign; rw [← Daisy.sparkPath, Sum.inr.injEq]
      by_cases he:Merge.Palette.mark M k=p
      · rw [if_pos he, if_pos (hx.mp he)]; unfold Merge.Palette.wages mcount; rw [hx.mp he]; unfold D;ring
      rw [if_neg he, if_neg (mt hx.mpr ?_)] -- direction! not p -> ¬sign
      · simp
      exact he
    exact Mixed.ready_vertices S Q.halo b X H.birth _ _ _ hT (Merge.Palette.toward M H t₀ hx0 hr hF ht z _ ⟨E.accrues.packetBound,h.nonneg,E.accrues.extra,h.hit⟩)
  have he z:tariff u w 0 Q.ε z=D*tariff g w (Mixed.stamp S X) Q.ε z := by unfold u tariff gale Mixed.stamp; simp only [Pi.zero_apply,add_zero,Real.exp_add]; ring
  have hz: Ready Z b (tariff u w 0 Q.ε) (Q.exp+2*Q.ε) (D*X.rootHit) Q.δ (1/2) := by rw [funext he]; exact ⟨mul_pos hD hv.1,Q.pos,hs,by norm_num,fun z=> mul_nonneg hD.le (hv.2.2.2.2.1 z), Quotes.hit_scale hD.le hv.2.2.2.2.2⟩
  intro x
  have hx i:0 ≤ w i:= by
    rcases i with i | i
    · exact mul_nonneg E.lives.extra (Nat.cast_nonneg _)
    exact Nat.cast_nonneg _
  have hp:= extraSets (n:=k) Z b u w Q.exp Q.ε (fun z=>mul_nonneg (mul_nonneg hD.le (hg _)) (Real.exp_pos _).le) hx Q.bound Q.usable hz x
  convert hp using 1; ext p
  · dsimp only; unfold Reserves.rooted; split
    next hv=>
      by_cases hg : H.ticketsP 0 0 0 p
      · rw [bought,if_pos hg,if_pos (show Ac.Spark Z p ∧ x∈p.biUnion Z from ⟨(H.attends _).1 hg,hv⟩), show (∏ i∈p,u i)=_ from hU p X.markSeed, show setPrice Z b w p=H.shapeW p from rfl, strongerN, currency]
        change _=(surge F' S p*(D^(pinsN ℓ S) p*gust S (Q.mark L μ s) D p*(∏ i∈p,φ i)))*Real.exp (Q.exp*coverNumber (radiusB s) (H.unionP p))*_*_; unfold D; ring
      rw [bought,if_neg hg,mul_zero,zero_mul,if_neg fun h=>hg ((H.attends _).2 h.1),zero_mul,zero_mul]
    next hx => rw [if_neg fun h=>hx h.2,zero_mul,zero_mul]
  rfl -- short form
end first
end YM.PhysicalNext.Repeat.Height

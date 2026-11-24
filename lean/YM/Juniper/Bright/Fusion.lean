import YM.Juniper.Bright.Ramp
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Revenue
/-!
 # Amplification by marked Price in the common real lemma.

 Auxiliary lemma for extending temperature $S$ buying reserves. Strength {
    (per old local sqrt pay on q), (per-supported-mark receipt),
   (by volume hit of old Reference root)} includes any cover exponent as in
 Upper Assembly. Prove a weighted Ξ.meant cap, NOT inheriting the old
 exponent-3 specialization. Prices can be reused for any placement. Proof
 follows the tariff lift in Census.Widow, needed here arbitrary-power, and
 nothing else necessary beyond its monetary Ready lemma ingredients. DO NOT
 USE if forgetting inputs or adding independent seeds.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge}

section Sets
variable {c:Side} {ι:Type*} (S:ι→Support c) (B:ℕ) (f E : ι→ℝ) (a ε:ℝ)

lemma keep_exp {h γ:ℝ} (m :ℕ)(hf:∀ i,0≤f i)(hE:∀ i,0≤ E i)(ha:0≤a)(hε:0<ε)(hp:Ready S B (tariff f E 0 ε) (a+2*ε) h γ (1/2)) (x: Site c):
      SumBudget (fun s:Finset ι=> Reserves.rooted S B f x a s * (1+setPrice S B E s)^m * Real.exp (ε*setPrice S B E s)) (extract ε m 0 0 * treeYield h (1/2) 0):= by
  have he:= touch_tail _ _ hp x 0
  simp only [Nat.zero_le, ↓reduceIte] at he
  rw [show extract ε m 0 0=polyPrice ε m by simp [extract]]
  refine budget_mono (budget_scale (show 0 ≤ polyPrice ε m by unfold polyPrice; positivity) he) (fun i=> ?_) fun z=> ?_
  · have ht:0≤Reserves.rooted S B f x a i:=by
      unfold Reserves.rooted; split
      next=> exact mul_nonneg (prod_nonneg fun i _=>hf _) (Real.exp_nonneg _)
      next => rfl
    exact mul_nonneg (mul_nonneg ht (pow_nonneg (add_nonneg zero_le_one (sum_nonneg fun i _=> add_nonneg (Nat.cast_nonneg _) (hE _))) _)) (Real.exp_nonneg _)
  let d : ℝ:=setPrice S B E z
  have hd:0≤d:=sum_nonneg fun i _=>add_nonneg (Nat.cast_nonneg _) (hE _)
  have hh: 0 ≤ polyPrice ε m := by unfold polyPrice; positivity
  unfold Reserves.rooted; rw [Reserves.set_exchange]
  unfold touches; split
  next he=>
    let X:= ∏ i∈z, f i; let g:= charge S B f a
    have hU:0≤(∏ i∈z,f i) * currency B a (z.biUnion S) := mul_nonneg (prod_nonneg fun _ _=>hf _) (Real.exp_pos _).le
    have hy:(∏ i∈z,f i)*currency B a (z.biUnion S) ≤ (∏ i∈z,g i):=by
       unfold g Ursell.charge currency; simp only [Finset.prod_mul_distrib,← Real.exp_sum,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Ac.cover S B he.1) ha)) (prod_nonneg fun i _=> hf _)
    simp only [Pi.zero_apply,sum_const_zero,add_zero]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul hy (polynomial_cost hε hd m) (by positivity : 0≤ (1+d)^m) (hU.trans hy)) (Real.exp_pos _).le).trans
    change _ ≤ _*((∏ i∈z,g i)*Real.exp (2*ε*d))
    rw [show 2*ε*d=ε*d+ε*d by ring,Real.exp_add]; apply le_of_eq; unfold d polyPrice; ring
  next hh=> rw [zero_mul,zero_mul,zero_mul,mul_zero]
end Sets

variable {c f L : Side} {P:Teller G} {S: StepData c f} {T: Tube G S} {R : Rep G f}
    {W μ x C A s v r a b y i d t:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W} {I:Cash W x μ L Q o C T R}
    {j n k : ℕ}

def boltKey (S:StepData c f) (f':Alphabet c f→ℕ): Head S→ℕ:= Sum.elim (fun _=>0) f'
def bill (S: StepData c f)(f':Head S→ℕ) (z:Molecule S) := ∑ x∈z,f' x

def strength (I:Cash W x μ L Q o C T R) (D₀ : ℝ) (f : Head S →ℕ) (u:Molecule S) := D₀^bill S f u*gust S (Q.mark L μ x) D₀ u * Real.exp (Q.ε*I.shapeW u)
variable {f' : Alphabet c f→ ℕ}
lemma contact {D₀ : ℝ}(Ξ:Utopia I j v d r A χ)(hD:1 ≤ D₀)(k:ℕ)(h: Sales (radiusB x) Q.relative Q.ε (footprints T R Q.halo (radiusB x)) (fun i=> D₀^f' i*Ξ.flair i) (Sum.elim (Raw.forcedExtra R) (Sum.elim (Coat.exCharge T R) fun _=>0)) (Q.goal L x))
    (hq: degreePrice (radiusB x) (D₀*(Q.costs L μ 1 x 0).rootHit) Q.δ ≤ 1/2) : Ac.Hit I.unionP (radiusB x) (fun p:Molecule S=>strength I D₀ (boltKey S f') p * Ξ.meant p k) Q.exp (D₀*Q.overture L μ x k):=by
  let K := boltKey S f'; let X:= Q.costs L μ R.beta x A
  let g (z: Head S):= D₀ ^ K z * Ξ.fare z; let u:=gale S X.markSeed D₀ g
  let p:= I.supportP; let B:= radiusB x; let w:= Mixed.lengths S X (lengths T R)
  have ht:Ready p B (tariff g w (Mixed.stamp S X) Q.ε) (Q.exp+2*Q.ε) X.rootHit Q.δ (1/2):= by
    let z y:= D₀ ^ f' y * Ξ.flair y
    suffices he:g=Mixed.costs S Q.halo B (steamP S X) z by rw [he]; exact Mixed.ready_vertices S Q.halo B X I.birth z (lengths T R) (steamP S X) Ξ.lives ⟨Ξ.accrues.packetBound,h.nonneg,Ξ.accrues.extra,h.hit⟩
    funext i; rcases i with i|i
    · simp only [g,K,boltKey,Sum.elim,pow_zero,one_mul]; rfl
    rfl
  have he:0<D₀:=zero_lt_one.trans_le hD
  have hu i:0≤u i:=mul_nonneg (mul_nonneg he.le (mul_nonneg (pow_nonneg he.le _) (Ξ.fares _))) (Real.exp_pos _).le
  have hz:Ready p B (tariff u w 0 Q.ε) (Q.exp+2*Q.ε) (D₀*X.rootHit) Q.δ (1/2):= by
     have hf z:tariff u w 0 Q.ε z=D₀*tariff g w (Mixed.stamp S X) Q.ε z := by unfold u tariff gale Mixed.stamp; simp only [Pi.zero_apply,add_zero,Real.exp_add]; ring
     rw [funext hf]; exact ⟨mul_pos he ht.1,Q.pos,hq,by norm_num,fun z=> mul_nonneg he.le (ht.2.2.2.2.1 z), Quotes.hit_scale he.le ht.2.2.2.2.2⟩
  intro x
  have hw i : 0 ≤ w i:= by
    rcases i with i|i
    · exact mul_nonneg Ξ.lives.extra (Nat.cast_nonneg _)
    exact Nat.cast_nonneg _
  convert keep_exp p B u w Q.exp Q.ε k hu hw Q.bound Q.usable hz x using 1
  · ext z; dsimp only; unfold Reserves.rooted; split
    next h=>
      by_cases hk:I.ticketsP 0 0 0 z
      · rw [Utopia.meant, if_pos hk, if_pos (show Ac.Spark p z∧ x∈z.biUnion p from ⟨(I.attends _).1 hk,h⟩),strength]; unfold u g
        simp only [gale, K, Finset.prod_mul_distrib,Finset.prod_const, Finset.prod_pow_eq_pow_sum,gust,bill]
        let x':=Q.ε; have hf:w=Mixed.lengths S I.faresP (lengths T R):= rfl
        rw [hf]; unfold Cash.numP; rw [Nat.cast_sum, ← Real.exp_sum, ← Finset.mul_sum]
        unfold currency; ring!
      rw [Utopia.meant, if_neg hk, mul_zero,zero_mul, if_neg fun h'=> hk ((I.attends _).2 h'.1),zero_mul,zero_mul]
    next hx => rw [if_neg fun h=>hx h.2,zero_mul,zero_mul]
  unfold ConnectedActivityE6.Target.overture ConnectedActivityE6.Target.quantum Mixed.Costs.ceiling Reserves.treeYield
  change D₀*(_ * ((X.rootHit*_)*_))=Reserves.extract _ _ _ _ *((D₀*X.rootHit)*_ *_)
  dsimp only [ConnectedActivityE6.Target.costs,Buy.quote]; norm_num; ring
end YM.Juniper.Bright

import YM.RG01.Survive.Landscape
import YM.RG01.Survive.Products

/-! # Second log aggregation of a scaled finite analytic expansion

Compile a low-load, no compulsory-share transmission at the *actual*
dictionary before reclosure into a rendered finite polynomial plus
Taylor/exceptional residual; lift all derivative charges at once to
complete BudgetPoint using a separate support rate for the position factor
and a separate output rate for later orbit/fusion. No summability of an
ansatz on the whole evaluated exponential is used. Hypotheses on the
leaf costs here are made deliberately explicit (including scalar leaves)
and are about integrated primitive entries through the stipulations, not a
comparison to Fk packets. Lifting these from unintegrated primitives
(including profile removals and the `last` residual) and pricing them
uniformly is a distinct upstream problem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Survive
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n j : ℕ} {R : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

/-- Use all ordinary entries 0,..,M and a charged tail at M+1. Subtract
before applying gauge/seat transforms; require honest measured functions
on each label so the formal vs physical gauge averaging is explicit. -/
abbrev Orders (M:ℕ):= Fin (M+2)
abbrev Expansions (H : Cash W s μ L Q o C T R) (M:ℕ):= H.ThinP → Orders M → Config G c → ℝ

structure LeafReady (χ:Chi) (K : ℕ) (length : ℝ) {M : ℕ} (x:Expansions H M)
    (v : ℝ) (j : ℕ) (u : H.ThinP → Orders M→ℝ) (total : H.ThinP → ℝ) (ρ : ℝ): Prop where
  letter (i p): Narrow K length i→
    GaugeInvariant (x i p) ∧ Measurable (x i p) ∧ LocalOn (H.smallAt i) (x i p)
  budget (i p): Narrow K length i→
    ∀ V, Healthy (Pressure.temp s) (H.smallAt i) V → Ore V (x i p) v (u i p) j
  scale : 1 ≤ ρ
  pos (i p): Narrow K length i→ 0 ≤ u i p
  bounds i : Narrow K length i→
    (∑ p, u i p * ρ^p.val) ≤ total i
  identity i : Narrow K length i→ ∀ V, leaflet H χ V i=∑ p, x i p V

/-- Require all constituent charges of a survivor, else discard (literal
stream vanishes identically by Narrow or was in the previous import set).
-/
def issued (K : ℕ) (length : ℝ) (z:H.fragrances):Prop :=
  short K length z ∧ ∀ i,Narrow K length (z.2 i)
abbrev atGrade {M : ℕ} {z:H.fragrances} (q:Option (Fin z.fst)→Orders M): ℕ:=
  Products.order (fun _ p=>(p:Orders M).val) q

def aliquot {M : ℕ} (y : Expansions H M) (z : H.fragrances) (q : Option (Fin z.fst)→Orders M)
    (U : Config G c) := ∏ i, y (z.2 i) (q i) U

def share (take : H.fragrances → ℕ→Prop) {M : ℕ} (y : Expansions H M) (K : ℕ) (length : ℝ)
    (z : H.fragrances) (U : Config G c) : ℝ :=
    if issued K length z then
      (coefficient H.seam z.2/(z.fst+1).factorial)*
        ∑ q ∈ univ.filter (fun q=> take z (atGrade q)), aliquot y z q U
    else 0

namespace LeafReady
variable {K M : ℕ} {l : ℝ} {y : Expansions H M} {v ρ : ℝ} {u : H.ThinP→Orders M→ℝ} {g:H.ThinP→ℝ}
    (h : LeafReady χ K l y v j u g ρ) (take:H.fragrances→ ℕ → Prop)
    (z:H.fragrances) (hl: ∀ i,Narrow K l (z.2 i))

include h
lemma recover (V:Config G c) :
    (if short K l z then stream H χ V z else 0) = share (fun _ p=> ¬take z p) y K l z V + share take y K l z V := by
  unfold share; by_cases ht: issued K l z
  swap; · rw [if_neg ht,if_neg ht]; split
          next hs=>
            have hf:stream H χ V z=0:= Classical.byContradiction (fun he=> ht ⟨hs,(narrows he K l hs).1⟩)
            simp only [hf,add_zero]
          simp
  rw [if_pos ht,if_pos ht,if_pos ht.1,stream,Gas.term, ← mul_add]
  let q i:= leaflet H χ V (z.2 i)
  rw [add_comm (Finset.sum ..) (Finset.sum ..), Finset.sum_filter_add_sum_filter_not] -- Decidable!
  have he: ∏ i,q i=∑ p,aliquot y z p V := by unfold q; simp_rw [h.identity _ (ht.2 _)]; exact Fintype.prod_sum (f:=fun i j=> y (z.2 i) j V)
  dsimp only [q] at he; rw [he]; ring

/-- Fix z with any selected retained grades all at or above p. Dropped z
has literal zero represented regular letter (before all masks).
-/
theorem charge (p : ℕ)(hp:∀ q, take z q→p≤q)(h0:∀ p, 0≤g p) :
    let Z:= reachability z
    let w:= share take y K l z
    GaugeInvariant w ∧ Measurable w ∧ LocalOn Z w ∧
      ∀ U, Healthy (Pressure.temp s) Z U →
        Ore U w v ((ρ^p)⁻¹*clusters H.seam (fun i=>2^j*g i) z.snd) j:=by
  intro Z w
  let a : ℝ:= coefficient H.seam z.2/(z.1+1).factorial
  let x:= clusters H.seam (fun i=>2^j*g i) z.snd
  have hx:0≤x:=clusters_nonneg _ (fun i=> mul_nonneg (by positivity) (h0 i)) _
  have hρ:0<ρ:=zero_lt_one.trans_le h.scale
  by_cases hi:issued K l z
  swap; · rw [show w=(fun _=>0) from funext fun _=> if_neg hi]
          refine ⟨fun _ _=> rfl,measurable_const, fun _ _ _=>rfl, fun U hu E _ _ _ X a hp he=> ?_⟩
          exact (Brush.certified (x:=a) zero_le_one 0).climb (by rw [norm_zero]; change _≤(ρ^p)⁻¹*x; positivity) le_rfl
  have hl i (p:Orders M):= h.letter (z.2 i) p (hi.2 i)
  let f (q : Option (Fin z.fst) → Orders M) := aliquot y z q
  let S':= univ.filter (fun q : Option (Fin z.fst) → Orders M=> take z (atGrade q))
  have hw : w=(fun U=> a*∑ q∈S', f q U):= funext fun _=> if_pos hi
  rw [hw]; refine ⟨fun t U=> ?_,measurable_const.mul (Finset.measurable_fun_sum _ (fun q _=> Finset.measurable_fun_prod _ (fun i _=> (hl i (q i)).2.1))),fun U V hu=> ?_,fun U hU E _ _ _ V m ht he=> ?_⟩
  · exact congr_arg _ (Finset.sum_congr rfl fun q _=> Finset.prod_congr rfl fun i _=> (hl i (q i)).1 t U)
  · have hx i : H.smallAt (z.2 i)⊆Z:= subset_biUnion_of_mem (H.smallAt ∘ z.snd) (mem_univ i)
    exact congr_arg _ (Finset.sum_congr rfl (fun q _=> Finset.prod_congr rfl (fun i _=> (hl i (q i)).2.2 U V (agrees_mono hu (Finset.coe_subset.mpr (hx i))))))
  have hx i t := h.budget (z.2 i) t (hi.2 i) U (show Healthy _ _ U from Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ z.snd) (mem_univ i)) hU)
  let F i t k := y (z.2 i) t (V k)
  have hg := Products.retains (x:=m) (j:=j) F (fun i=>u (z.2 i)) (fun i=>g (z.2 i)) ρ (fun (_i:Option (Fin z.fst))(q:Orders M)=>q.val) (fun q=>take z (atGrade q)) (fun i t=> hx i t E V m ht he) p (fun _ h=> hp _ h) h.scale (fun q=> h.bounds (z.2 q) (hi.2 q))
  have ha:0≤((z.1+1).factorial:ℝ):=Nat.cast_nonneg _
  rw [show ((fun (U:Config G c)=> a* ∑ q ∈ S', f q U) ∘ V)=(fun k=> a*Products.filtered F (fun q:Option (Fin z.fst)→Orders M=> take z (atGrade q)) k) from by ext; simp [Products.filtered,F,S',Products.atGrades,f,aliquot]; left; congr! 4]; change Brush _ ((ρ^p)⁻¹*x) 1 (fun k=> a*Products.filtered F (fun q:Option (Fin z.fst)→Orders M=> take z (atGrade q)) k) m
  convert! hg.smul a using 1
  unfold x a clusters; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg ha]; ring

/-- Position-weighted derivative envelope after charting. -/
def allowance (b:BudgetPoint)(z: H.fragrances)(j s':ℕ) (g:H.ThinP→ℝ):ℝ:=
  (shiftG s*(1+(coverNumber b.B (reachability z):ℝ)))^(j*s') * clusters H.seam (fun i=> 2^j*g i) z.snd

/-- On real coarse fields after summing ALL ($V$-independent) letter-grade assignments. -/
lemma germs (b:BudgetPoint) (hs:b.threshold=Pressure.temp s) (hj : b.order ≤ j) (hB:b.B=radiusB s) (q:ℝ) (hq:0≤q)
    (hS:Sailor G b.threshold q j)(hr : j*q ≤ v)(hv : 0 < v)
    (w:ℕ)(hw:b.power≤w) (x:Site c)(hx:x∈reachability z) (p:ℕ)(hp:∀ q,take z q→p≤q)(h0:∀ p,0≤g p):
    let Z:= reachability z
    let L := share take y K l z
    b.Regular Z L ∧ b.supBounds x Z L ((ρ^p)⁻¹*allowance b z j w g):= by
  intro Z L
  obtain ⟨hi,hm,hL,ht⟩:= h.charge take z p hp h0
  have he:=clusters_nonneg H.seam (fun i=> mul_nonneg (by positivity : (0:ℝ)≤2^j) (h0 i)) z.2
  have hg:0<ρ:=zero_lt_one.trans_le h.scale
  let A:= clusters H.seam (fun i=>2^j*g i) z.2
  have hh U (hhU: Healthy b.threshold Z U) : ContDiffAt ℝ (↑b.order) (L ∘ increment U) 0:= (charted (ht U (hs ▸ hhU)) hv).of_le (by exact_mod_cast hj)
  let d:ℝ := shiftG s*(1+ ↑(coverNumber b.B Z))
  have hK : 1 ≤ d:= by
    unfold d; unfold shiftG
    nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber b.B Z), Nat.cast_nonneg (α:=ℝ) (radiusB s)]
  refine ⟨⟨hL,hm,hi,hh,fun U h a ℓ e=> Next.Foundations.left_has a e (hh U h)⟩,⟨mul_nonneg (by positivity) (mul_nonneg (pow_nonneg (zero_le_one.trans hK) _) he),fun U h ℓ he' hD=>?_⟩⟩
  have h0 : ∀ y∈Z, 1+(separation y x :ℝ)≤d:= by
    intro y hy
    have hf := Corona.extent Z b.B hy hx
    unfold d shiftG; rw [← hB]
    exact le_trans (show _ ≤ 1+(((coverNumber b.B Z)*(4*b.B+2) +2*b.B:ℕ):ℝ) by exact add_le_add_right (by exact_mod_cast hf) _) (by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber b.B Z),Nat.cast_nonneg (α:=ℝ) b.B])
  have hn := costsD (p:=b) (Y:=d) hL hS hq x _ hr (ht _ (hs ▸ h)) h0 hK ℓ (he'.trans hj) hD
  apply le_trans hn _; change d^(b.power*j)*((ρ^p)⁻¹*A) ≤ (ρ^p)⁻¹*(d^(j*w)*A)
  rw [mul_left_comm, Nat.mul_comm b.power]
  gcongr

/-- The output anchored-log component price. -/
theorem clearing (b:BudgetPoint) (w δ β:ℝ)(a:ℝ) -- γ unused remove
    (hs:b.threshold=Pressure.temp s)(hB:b.B=radiusB s) (hj:b.order≤j) (n:ℕ)(hn:b.power≤n)
    (q:ℝ)(hq:0≤q)(hS:Sailor G b.threshold q j)(hr:j*q≤v)(hv:0<v)
    (hA: AnalyticBridge.VerifiedReset.Quotes.preExponent b ≤ a)
    (hδ:0<δ)
    (hY:Ready H.smallAt b.B (fun i=>2^j*g i) (a+δ) w δ β)
    (r:ℕ)(he:∀ z n,take z n → r ≤ n):
    AnalyticBridge.VerifiedReset.Quotes.early b (Song.locate H) (fun z=>(ρ^r)⁻¹*allowance b z j n g)
      ((ρ^r)⁻¹*(collars G δ s j n*(w*(1-β)⁻¹))) ∧
       ∀ z,b.Regular (reachability (H:=H) z) (share take y K l z) ∧ b.supBounds (Song.locate H z).site (Song.locate H z).support (share take y K l z) ((ρ^r)⁻¹*allowance b z j n g):=by
  let Z:=reachability (H:=H)
  let u:= (ρ^r)⁻¹; have hu:0<u:=by unfold u; have hf:=zero_lt_one.trans_le h.scale; positivity
  have hp:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hg i : 0≤g i:=nonneg_of_mul_nonneg_right (hY.2.2.2.2.1 i) (by positivity : (0:ℝ)<2^j) -- lemma?
  have hx z:= h.germs take z b hs hj hB q hq hS hr hv n hn (Song.locate H z).site (Song.locate H z).anchor r (he z) hg
  refine ⟨fun x=> ?_,hx⟩
  have hK:0≤a+δ:= add_nonneg ((show (0:ℝ)≤AnalyticBridge.VerifiedReset.Quotes.preExponent b from by unfold AnalyticBridge.VerifiedReset.Quotes.preExponent; have h:=b.exponent_pos; positivity).trans hA) hδ.le
  have hz:=Ursell.log_hit_tail _ _ _ H.testS hY hK 0 x
  simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
  let v:= collars G δ s j n
  have ht:0≤v:=by unfold v collars Reserves.polyPrice; positivity
  have hh := budget_scale hu.le (budget_scale ht hz)
  refine budget_mono hh (fun z=>?_) fun z=> ?_
  · dsimp only; split
    next=> exact mul_nonneg ((hx z).2.1) (Real.exp_pos _).le
    exact le_rfl
  dsimp only; split
  next hy=>
    have hv: x∈ Z z:=hy ▸ (Song.locate H z).anchor
    let t:ℝ:=coverNumber b.B (Z z)
    let Hq:= clusters H.seam (fun i=>2^j*g i) z.snd
    have hu':0≤Hq := clusters_nonneg _ (fun i=>mul_nonneg (by positivity) (hg _)) _
    have he':0≤t:=Nat.cast_nonneg _
    rw [if_pos (show x∈unionOf H.smallAt z.2 from hv)]; change u*((shiftG s*(1+t))^(j*n)*Hq) * Real.exp (_*t) ≤ u*(v*(Hq*Real.exp ((a+δ)*t)))
    unfold v collars
    rw [Nat.mul_comm j n,mul_pow,add_mul a, Real.exp_add]
    have h := polynomial_cost hδ he' (n*j)
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (pow_nonneg hp _)) hu') hu.le) (Real.exp_pos _).le)
    unfold Reserves.polyPrice
    nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA he'))
      (show 0≤u*(((shiftG s)^(n*j)*(δ⁻¹^(n*j)* ↑((n*j).factorial) * Real.exp δ*Real.exp (δ*t)))*Hq) by positivity)]
  exact hh.1 z
end LeafReady
end YM.RG01.Survive

import YM.RGComparison01.Divides

/-!
# Exceptional paid on actual held supports

 earlyValue identity still to combine. Use for any self-enabled Captain in
 the same Cash seats. Choice of dashboard moves paid **at site chosen**.
 No order-position probes read at larger supports for these payments. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Divides
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Opacity
open PhysicalNext PhysicalNext.Repeat Height Song Brim Beam
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Selector Beacon
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ}
    {k j n ℓ : ℕ} {χ : Chi} {H : Cash W s μ L Q o α T R}
variable (p : BudgetPoint)
    (N : Captain H j C' d v Y A b r B q k χ)

def hires (H : Cash W s μ L Q o α T R) (Ω : ℕ → Prop) (z : Magazine H) : Prop :=
    z.elim (fun i=>Inherited Ω i) (fun _=>False)
def meter (H : Cash W s μ L Q o α T R) (Ω : ℕ→Prop) (ℓ n : ℕ) (z : Magazine H) : Prop :=
    z.elim (fun i=> ¬Inherited Ω i ∧ Weeds ℓ i) (fun i=> n ≤ Meadow.arc T.down i)

lemma hop {f : Magazine H → Config G c → ℝ} {a b : ℝ} (p : BudgetPoint)
    (h : Meadow.Budget p (Beam.dashboard H) (f ∘ Sum.inl) a)
    (hv : Meadow.Budget p (strings T.down p) (f ∘ Sum.inr) b) :
    Meadow.Budget p (Beam.contents H p) f (a+b) := by
  obtain ⟨u,h,hu⟩:=h; obtain ⟨v,hV,hv⟩:=hv
  exact ⟨Sum.elim u v, fun i=> Cost.sum (h i) (hV i), Sum.rec hu hv⟩

lemma needle (Ω : ℕ→Prop) (p : BudgetPoint) (Kg : ℝ) {K : ℝ}
    (h : Meadow.Budget p (Beam.dashboard H) (byLog (Inherited Ω) χ) K) :
    Meadow.Budget p (Beam.contents H p) (bySong (hires H Ω) χ Kg) K := by
  have hv : Meadow.Budget p (strings T.down p) (bySong (hires H Ω) χ Kg ∘ Sum.inr) 0 := by
    rw [show bySong (hires H Ω) χ Kg ∘ Sum.inr=0 from funext fun x=> if_neg (fun h=>h)]
    refine ⟨0,fun i=> ?_,fun i=> ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const _) (abs_zero.le)⟩⟩
    simp [SumBudget]
  exact (add_zero K) ▸ hop p (by rw [atLog]; exact h) hv

include N
lemma whole {i : ℝ} (γ : ℝ)
    (hp : p.threshold=Pressure.temp s) (hB : p.B=radiusB s)
    (hj:p.order≤j) (hn:p.power ≤ n) (hr: preExponent p ≤ a) (hx : Armada Q L μ a s i B j k)
    {σ C Λ : ℝ} (hT : T.down.Bounds T.low σ C Λ) (hd : WilsonStartup.Decent T.low p)
    (he : preExponent p / p.B ≤ σ/4) :
    Meadow.Budget p (Beam.contents H p) (opus H (selfA H) χ γ)
      ((collars G i s j n*(salary Q L μ B s j k*(1-1/2)⁻¹))+octaveNeed G p T.low σ C Λ R.beta γ):= by
  have hv := hx.applies N n 0; simp only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] at hv
  have hw := bookLog p N (n:=n) (a:=a) (fun _=>True) hp hB hj hn hr (by simpa only [↓reduceIte] using hv)
  apply hop
  · refine (show byLog (fun _:H.fragrances=>True) χ= opus H (selfA H) χ γ ∘ Sum.inl from ?_) ▸ hw
    funext i; rw [byLog, if_pos True.intro]; rfl
  rw [show opus H (selfA H) χ γ ∘ Sum.inr=bySong (meter H (fun _=> True) 0 0) χ γ ∘ Sum.inr from funext fun i=> by symm; exact (if_pos (show meter H (fun _=>True) 0 0 (.inr i) from Nat.zero_le _))]
  obtain ⟨f,h,hF⟩:= Meadow.lent (c:=c) p T.down T.low R.beta γ hT hd he
  refine ⟨f,fun x=> ?_,fun i=>?_⟩
  · have hb:= Meadow.arch_tail (strings T.down p) p _ h (by have hw := hT.width; positivity) (fun i => (hF i).2.1) (k:=0) x
    simpa only [Nat.zero_le, ↓reduceIte,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using hb
  rw [Function.comp_apply,bySong,if_pos (show meter H (fun _=>True) 0 0 (.inr i) from Nat.zero_le _)]
  exact hF i

local notation "gZ" => Height.grow G L s
section tail
variable (V : ℕ → ℝ) (t : ℝ) (ht : 1≤t) (hV : ∀ i,1 ≤ V i) {γ sl : ℝ} (hd : 1 ≤ Height.grow G L s)
variable (Sel : ℕ → Prop)
include ht hV hd
lemma met (l K : ℕ) (he : gZ^l ≤ t) (hp : p.threshold = Pressure.temp s) (hB : p.B=radiusB s) (hj : p.order ≤ j)
    (hn : p.power ≤ n) (hr : preExponent p ≤ a) (hS : gZ ^ l ≤ Real.exp (Q.mark L μ s))
    (hZ : gZ ^ l ≤ Real.exp (Q.ε*radiusB s)) (hP : Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z => spire V t z * N.markΦ z n) a sl)
    {σ C Λ : ℝ} (hT : T.down.Bounds T.low σ C Λ) (hD : WilsonStartup.Decent T.low p)
    (hE : preExponent p / p.B ≤ σ/4):
    Meadow.Budget p (Beam.contents H p) (bySong (meter H Sel l K) χ γ)
      ((gZ^l)⁻¹*sl + Real.exp (-(σ/4)*K) * octaveNeed G p T.low σ C Λ R.beta γ) := by
  apply hop
  · rw [atLog]; apply bookLog p N (n:=n) (a:=a) _ hp hB hj hn hr; exact recover_spire N V t _
      (pow_pos (zero_lt_one.trans_le hd) _) (fun i hi=> weeds_pay V hV t ht hd he hS hZ i (show ¬Inherited Sel i∧_ from hi).2) hP
  obtain ⟨f,h,hF⟩:= Meadow.lent (c:=c) p T.down T.low R.beta γ hT hD hE
  let g i:= if K ≤ Meadow.arc T.down i then f i else 0
  refine ⟨g,fun i=> Meadow.arch_tail (strings T.down p) p _ h (by have hw:=hT.width; positivity) (fun i=> (hF i).2.1) (k:=K) i,fun i=>?_⟩
  by_cases hv:K ≤ Meadow.arc T.down i
  · rw [Function.comp_apply, bySong, if_pos (show meter H Sel l K (.inr i) from hv), show g i=_ from if_pos hv]
    exact hF i
  rw [Function.comp_apply, bySong, if_neg (show ¬ meter H Sel l K (.inr i) from hv), show g i=_ from if_neg hv]
  exact ⟨CouplingShape.reg_const _, sup_le (CouplingShape.sup_const _) (abs_zero).le⟩

omit V hV in
lemma prices_hi {u : ℝ} (hu : 1 ≤ u) (hp : p.threshold=Pressure.temp s) (hB : p.B=radiusB s)
    (hj : p.order ≤ j) (hn : p.power ≤ n) (hr : preExponent p ≤ a) (hS : gZ^3 ≤ Real.exp (Q.mark L μ s))
    (hZ : gZ ^ 3 ≤ Real.exp (Q.ε*Pressure.Stores.till s)) (hP : Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z => spire (Tithe.bonus Sel u) t z*N.markΦ z n) a sl) :
    Meadow.Budget p (Beam.dashboard H) (byLog (fun z : H.fragrances=> (Inherited Sel z) ∧ Height.tired H z) χ)
      ((u * gZ^3)⁻¹*sl) := by
  apply bookLog p N _ hp hB hj hn hr
  apply recover_spire N (Tithe.bonus Sel u) t _ (mul_pos (zero_lt_one.trans_le hu) (pow_pos (zero_lt_one.trans_le hd) 3)) _ hP
  rintro z ⟨hv,h⟩
  apply mul_le_mul (bounty hu hv t ht) _ (pow_nonneg (zero_le_one.trans hd) 3)
    (zero_le_one.trans (hu.trans (bounty hu hv t ht)))
  rcases h with h|h|h
  · exact Beacon.cashout hd hS hZ z (Or.inl h)
  · exact Beacon.cashout hd hS hZ z (Or.inr (Or.inl h))
  have hx : 0 ≤ Q.mark L μ s:= H.laws.acquired.marked
  apply (hZ.trans (Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le))).trans
  exact le_mul_of_one_le_left (Real.exp_nonneg _) (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hd) (Real.one_le_exp (mul_nonneg hx (Nat.cast_nonneg _))))
end tail
end YM.RGComparison01.Divides

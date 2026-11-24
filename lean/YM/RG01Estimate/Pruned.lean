import YM.RG01Estimate.VacuumAcquire

/-!
# Record the support alignment. Earlier family measure uses this EXACT log cell ledger,
with terms at `Fate.steps` from both e, log and path. Unmarked only. Long path-book charges
from the orbit budget (extra geometry paid before wire). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Pruned

open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Meadow
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Expense Reprice
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Acquire

variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ s a α : ℝ} {i j k m n : ℕ} {χ : Chi}

variable (H : Cash W s μ L Q o α T R) (p : BudgetPoint) (χ : Chi) (M : Alliance H H 1 0)
    (E : Set ℕ) (r : ℕ)
def chosen : Magazine H → Prop := Sum.elim (fun z=> Fate.showcase E (Fate.steps r) (M.furrow z))
    (fun i=> Meadow.arc T.down i ≤ radiusB s)

-- extra path budget unmarked
variable (γ : ℝ)
def regLow (i : Magazine H) := if chosen H M E r i then opus H M χ γ i else 0
def regHigh (i : Magazine H) := if chosen H M E r i then 0 else opus H M χ γ i
def low : Collection.Source G c := ⟨choir (regLow H χ M E r γ) ∘ pennant H, (plusone H M χ γ).hardRead⟩
def high : Collection.Source G c := ⟨choir (regHigh H χ M E r γ) ∘ pennant H, (plusone H M χ γ).hardRead⟩

variable (hP : p.threshold=Pressure.temp s) (hB : p.B=radiusB s)
variable (hx : M.units=Equiv.refl _) {η θ A v σ Λ C a' b : ℝ}

-- split finances, with forward still full
variable (hd : Fate.Admission Q L W μ a o j m r χ s) (h : Stamp T) (hj:p.order ≤ j)
    (hp : p.power ≤ m) (hf : Cash.Renewed n a a' b H) (hr : T.down.Bounds T.low σ C Λ)
    (hy : WilsonStartup.Decent T.low p) (ht : preExponent p / p.B ≤ σ/4) (he : preExponent p ≤ a)
include hB hr hy ht
lemma path_tail : Budget (c:=c) p (strings T.down p) (fun i=> if radiusB s < Meadow.arc T.down i then sounding T.down T.low R.beta γ i else 0)
    (Real.exp (-(σ/4)*p.B)*Song.octaveNeed G p T.low σ C Λ R.beta γ) := by
  obtain ⟨f,hP,hQ⟩:= Meadow.lent (c:=c) p T.down T.low R.beta γ hr hy ht
  let g i:= if radiusB s< Meadow.arc T.down i then f i else 0
  have hL : Quotes.early p (strings T.down p) g (Real.exp (-(σ/4)*p.B)*Song.octaveNeed G p T.low σ C Λ R.beta γ) := by
    intro i
    have hp:=Meadow.arch_tail (σ:=σ/4) _ p _ hP (by have h:=hr.width; positivity) (fun i=> (hQ i).2.1) (k:=p.B) i
    refine budget_mono hp (fun i=>?_) fun i=>?_
    · dsimp only; split
      next => apply mul_nonneg _ (Real.exp_pos _).le
              unfold g; split; exact (hQ _).2.1; exact le_rfl
      exact le_rfl
    dsimp only; split
    next hi =>
      unfold g
      split
      next ht=> rw [if_pos (show p.B≤_ from hB ▸ ht.le)]
      rw [zero_mul]; split; exact mul_nonneg (hQ _|>.2.1) (Real.exp_nonneg _); simp
    exact le_rfl
  refine ⟨g,hL,fun i=>?_⟩
  dsimp only; unfold g; split; next => exact hQ i
  next => refine ⟨CouplingShape.reg_const _,?_⟩
          simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (o:=(strings T.down p i).site) (X:=(strings T.down p i).support) 0)

include hd h hf hP hj hp he ht
-- record full kept bound at least quantitatively per-stage.
omit hd h hf in
lemma budget_all (i B':ℝ) (k : ℕ) {y' d' v' t A b' r' q : ℝ} (N : Captain H j y' d' v' t A b' r' B' q k χ)
    (hb : Armada Q L μ a s i B' j k) :
    Budget p (contents H p) (opus H M χ γ) ((collars G i s j m*(salary Q L μ B' s j k*(1-1/2)⁻¹)) + octaveNeed G p T.low σ C Λ R.beta γ) := by
  have hx:= hb.applies N m 0; simp only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] at hx
  have hu : Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun t=> if (fun _=> True) t then N.markΦ t m else 0) a
      ((collars G i s j m*(salary Q L μ B' s j k*(1-1/2)⁻¹))) := by simpa using! hx
  have hv : Budget p (dashboard H) (Song.sequence H M χ) (collars G i s j m*(salary Q L μ B' s j k*(1-1/2)⁻¹)) := by
    simpa using! (from_hit (Z:=fun _=> True) H χ M hP N hj hp hB he (by simpa using! hu))
  obtain ⟨f,hf,hF⟩:= stanzaReady (n:=c) T.down T.low p R.beta γ hr hy (ht.trans (show _ /4 ≤ σ/2 by have h:=hr.width; linarith))
  exact budget_concat hv (show Budget p (strings T.down p) _ _ from ⟨f,hf,hF⟩)

-- use for any input `q'` allowance for path costs. Truth relatives
include hx
variable {c' u : ℝ}
theorem account (hw : Real.exp (-(σ/4)*p.B)*Song.octaveNeed G p T.low σ C Λ R.beta γ ≤ u) (hi: preExponent p ≤ η)
    (hδ : Inherit.Debits R E (Fate.debt r G L s)) (hτ : Single.Pays H p E χ η θ) :
    Collection.Local (marquee H p) p (high H χ M E r γ) (turnFee p*(θ + (Fate.target r G L s + Fate.target r G L s)+u))
      (Cash.armK Q L μ s 0 n) ∧
    ∃ w, Collection.Local (marquee H p) p (low H χ M E r γ) w (Cash.armK Q L μ s 0 n) ∧
      Collection.Local (marquee H p) p (plusone H M χ γ) w (Cash.armK Q L μ s 0 n) := by
  obtain ⟨y',d',v',t,A,b,r',B',q,i,k,N,hP',ht'⟩:= (hd.2 c f S T h R α H).1
  let Z:= (marquee H p)
  let w:= ((collars G i s j m*(salary Q L μ B' s j k*(1-1/2)⁻¹)) + octaveNeed G p T.low σ C Λ R.beta γ)
  let D:= turnFee p; let β:= Cash.armK Q L μ s 0 n
  let f0:=plusone H M χ γ
  let W:= chosen H M E r
  have hg (f : Magazine H→ Config G c→ℝ) {q : ℝ} (h : Budget p (contents H p) f q) :
      Collection.Local Z p ⟨choir f ∘ pennant H,f0.hardRead⟩ (D*q) β := by
    obtain ⟨v,hv,h'⟩:=h
    exact VacuumListing.to_local H p χ M hP hB he hf f v hv h'
  have hc := remainder H χ M hP hB he E r hd hj hp hδ h
  have hl:= inherit_budget H χ M hx hP hB hi N E (Fate.steps r) hj hp hτ
  have ha : Budget p (contents H p) (opus H M χ γ) w := budget_all H p χ M γ hP hB hj hp hr hy ht he i B' k N ht'
  refine ⟨hg _ ?_, D*w, hg _ (budget_cut W ha), hg _ ha⟩
  let u' (i:Songbook c) := if radiusB s < Meadow.arc T.down i then sounding T.down T.low R.beta γ i else 0
  have hu' : Budget p (strings T.down p) u' u := by
    obtain ⟨v,hv,h'⟩:= path_tail (R:=R) p γ hB hr hy ht -- args
    exact ⟨v,fun i=>budget_loosen (hv i) hw,h'⟩
  refine Eq.mp ?_ (budget_concat (branch_budget (fun z=> Groups.isolation E (Fate.steps r) H (M.furrow z)) hl hc) hu'); congr 1
  funext t
  rcases t with t|t
  · dsimp only [Sum.elim]; unfold regHigh; by_cases h : Groups.isolation E (Fate.steps r) H (M.furrow t)
    · rw [if_pos h, if_pos h, if_neg (show ¬ chosen H M E r (.inl t) from Fate.disjoint E _ _ h.1)]
      rfl
    rw [if_neg h]; by_cases hv : Fate.showcase E (Fate.steps r) (M.furrow t)
    · rw [if_neg (show ¬ Groups.bad_renewal E (Fate.steps r) (M.furrow t) from fun h=>h (Or.inr hv)), if_pos (show chosen H M E r (.inl t) from hv)]
    rw [if_pos (show Groups.bad_renewal E (Fate.steps r) (M.furrow t) from not_or.mpr ⟨h,hv⟩), if_neg (show ¬ chosen H M E r (.inl t) from hv)]
    rfl
  dsimp only [Sum.elim]; unfold u' regHigh chosen; dsimp only [Sum.elim]; split_ifs <;> first| rfl| omega

omit h hx hP hf hB hd hj hp hr hy ht he
lemma tracks : (plusone H M χ γ).logRead=(low H χ M E r γ).logRead + (high H χ M E r γ).logRead := by
  have hf i : opus H M χ γ i=regLow H χ M E r γ i +regHigh H χ M E r γ i:= by unfold regHigh regLow; split <;> simp
  ext x i; let u:= pennant H x; let z:=u.1.view i; change Song.Rim c * opus H M χ γ u.2 z= Song.Rim c * regLow H χ M E r γ u.2 z + Song.Rim c * regHigh H χ M E r γ u.2 z
  rw [hf,Pi.add_apply,mul_add]

end YM.RG01Estimate.Pruned

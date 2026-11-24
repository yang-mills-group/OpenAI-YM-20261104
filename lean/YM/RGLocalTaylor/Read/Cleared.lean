import YM.RGLocalTaylor.Read.Tower

/-!
# Budget all dependencies on a fixed panel and buy support after localized relocation

Use `Quotes.early` across E-generation and for all of the members used
in Rain, so the norm we've earned also bounds any finite grouping after its
post-translation costs. Full-sum lemma only for summing scalars per site (extensive
bound), not for orbit prices which still need separate support/algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Read
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield Animals
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Boulevard
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R} {U : ℕ → RegularAddress c}
open RG01.Survive
variable {p : BudgetPoint} {v v' w : ℕ → Config G c→ℝ} {r q : ℝ}

variable (z z':ℝ)

abbrev orient (p:BudgetPoint)(U : ℕ → RegularAddress c)(v:ℕ→ Config G c→ℝ) (z:ℝ) := Meadow.Budget p U v z
namespace orient
variable (h: orient p U v r) (he: orient p U v' q)
include h
lemma widen (hp:r≤q): orient p U v q:=by obtain ⟨g,h,t⟩:=h; exact ⟨g,fun i=> budget_loosen (h i) hp,t⟩
lemma absolute : ∃ g : ℕ→ℝ, SumBudget g ((Fintype.card (Site c):ℝ)*r) ∧ ∀ i, p.Regular (U i).support (v i) ∧ p.supBounds (U i).site (U i).support (v i) (g i):=by
  obtain ⟨g,h,t⟩:=h; exact ⟨g,planetary h (fun i=> (t i).2.1),t⟩
lemma nonneg : 0 ≤ r:= by obtain ⟨g,h,t⟩:= h; exact Cost.nonneg (h 0)
lemma partialPoints (I : Finset ℕ) :
    p.Regular univ (∑ i∈I,v i) ∧ ∀ V: Config G c, flags p.threshold V=∅ → ∀ (l:List (Directions G c)),l.length ≤ p.order →
      (∀ i∈l, ‖i‖≤p.threshold) → ‖leftDerivs (∑ i∈I,v i) l V‖ ≤ (Fintype.card (Site c):ℝ)*r:= by
  obtain ⟨f,h,hF⟩:= orient.absolute h
  have hv i := (hF i).1; refine ⟨Meadow.regularA _ (fun i _=> reg_larger (hv i) (subset_univ _)),fun V hg l he hf=>?_⟩
  have hV i:Healthy p.threshold (U i).support V:=by unfold Healthy; rw [hg]; simp
  rw [Push.Local.left_sum _ _ _ _ (fun i _=> (hv i).smooth _ (hV i)) he]; exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=> (hF i).2.2 V (hV i) l he (fun k hk=> tiny (hf k hk) _))).trans (budget_sum h I))
lemma flat_tsum : Summable (fun i=> v i 1) ∧ ‖∑' i,v i 1‖ ≤ (Fintype.card (Site c):ℝ)*r := by
  obtain ⟨g,h,t⟩:= orient.absolute h
  have he i: ‖v i 1‖≤ g i:= (t i).2.2 1 (flat_ok ..) [] (by simp) (by simp)
  have hh:= budget_mono h (fun i=> norm_nonneg _) he
  exact ⟨Summable.of_norm hh.2.1,(norm_tsum_le_tsum_norm hh.2.1).trans hh.2.2⟩
include he
lemma subtract : orient p U (v-v') (r+q) := by
  obtain ⟨f,hf,hw⟩:=h; obtain ⟨g,hg,he⟩:=he
  refine ⟨f+g,fun i=> ?_,fun i=>⟨CouplingShape.reg_sub (hw i).1 (he i).1,CouplingShape.sup_sub (hw i).1 (he i).1 (hw i).2 (he i).2⟩⟩
  convert! budget_plus (hf i) (hg i) using 1; ext; dsimp only [Pi.add_apply]; split_ifs <;> ring
end orient

open PhysicalNext.Repeat.Meadow
namespace Pane

variable (H p)
def uptake (n:ℕ) (V : Collection.Source G c) :Collection.Source G c:={ V with logRead:=fun i=>if i∈ Meadow.panel H n then 0 else V.logRead i }
def panelist (n:ℕ) (V : Collection.Source G c) (x:Site c) : Config G c → ℝ := ∑ i∈Meadow.panel H n, Meadow.garnerAt H p x i • (V.logRead i)

variable {H p} {v v' w : Collection.Source G c} (hm:w.logRead=v.logRead+v'.logRead)
include hm
lemma restored : (uptake H n w).logRead=(uptake H n v).logRead+(uptake H n v').logRead:= by
  ext i V; unfold uptake; dsimp only [Pi.add_apply]; split; · change (0:ℝ)=0+0; ring
  rw [hm]; rfl
lemma atPanel : panelist H p n w=panelist H p n v+panelist H p n v':= by ext i U; unfold panelist; rw [hm]; simp only [Pi.add_apply,Finset.sum_apply, smul_add,Finset.sum_add_distrib] -- check grouping
omit hm
variable {q p' : ℝ} (hp: orient p (Beam.marquee H p).reg v.logRead p')
include hp
lemma upright : orient p (Beam.marquee H p).reg ((uptake H n v).logRead) p':= by
  obtain ⟨g,hg,hT⟩:= hp; refine ⟨g,hg,fun i=>?_⟩
  unfold uptake; dsimp only; split
  next=> exact ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const 0) ((abs_zero (α:=ℝ)).symm ▸ (hT i).2.1)⟩
  exact hT i

-- for any displacement application in the Rain local gauge argument.
def PanelQuality {c:Side} (p:BudgetPoint) (V : Trio.Offer G c) (x : ℝ) :=
  p.Regular univ (Trio.froth V) ∧ ∀ U:Config G c, flags p.threshold U=∅ → ∀ (l:List (Directions G c)), l.length ≤ p.order →
      (∀ i∈l, ‖i‖≤p.threshold) → ‖leftDerivs (Trio.froth V) l U‖ ≤ x
lemma evaluated : PanelQuality p (panelist H p n v) ((Fintype.card (Site c):ℝ)*p') := by
  unfold PanelQuality; let Q i:=∑ x:Site c,panelist H p n v x i
  rw [show Trio.froth (panelist H p n v)=∑ i∈Meadow.panel H n,v.logRead i from ?_]
  · exact orient.partialPoints hp ..
  ext i; unfold Trio.froth panelist; simp_rw [Finset.sum_apply]; rw [Finset.sum_comm]; exact sum_congr rfl fun j hj=> by simp_rw [Pi.smul_apply,← sum_smul,Meadow.paysOne]; rw [one_smul]

-- This estimate grants τ in the same recipe: no expansive Vol charge.
lemma panelPoint (ht : p.B=Pressure.radiusB s) (x:Site c) : ‖panelist H p n v x 1‖ ≤ (ballCost (Meadow.studio Q.halo (radiusB s)):ℝ)*p':= by
  have hh:=orient.nonneg hp
  obtain ⟨a,hG,h⟩:=hp; let D:= Beam.marquee H p; let f i:= v.logRead i 1
  let R i:= Meadow.garnerAt H p x i; let I:= Meadow.panel H n; unfold panelist; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply,smul_eq_mul]
  let d:= Meadow.studio Q.halo (radiusB s); let S:= neighbors d x; let E i x:= if (D.reg i).site=x then a i * Real.exp (preExponent p * coverNumber p.B (D.reg i).support) else 0
  apply le_trans (norm_sum_le ..)
  calc
    _ ≤ ∑ i∈ I, ∑ x∈S,E i x:= by
        apply sum_le_sum; intro i hi; by_cases H' : R i=0
        · change ‖R i*f i‖≤ _; rw [H',zero_mul,norm_zero]; exact sum_nonneg fun y _=> (hG y).1 i
        have he:= (Meadow.assigned H p x i hi ht H').2
        rw [norm_mul, Real.norm_of_nonneg (Meadow.nonnegative ..)]; apply (mul_le_of_le_one_left (norm_nonneg _) (Meadow.portions ..)).trans
        apply ((h i).2.2 1 (flat_ok ..) [] (by simp) (by simp) : ‖f i‖≤ a i).trans
        apply (le_mul_of_one_le_right ((h i).2.1) (Real.one_le_exp (show 0≤preExponent p * coverNumber p.B (D.reg i).support from mul_nonneg (Song.headline p).exponent_pos.le (Nat.cast_nonneg _)))).trans
        unfold E; rw [sum_ite_eq,if_pos (he (D.reg i).anchor)]
    _ ≤ (ballCost d:ℝ)*p':= by
        rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=> budget_sum (hG x) I))
        rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) hh
end Pane
end YM.RGLocalTaylor.Read

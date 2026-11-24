import YM.Contacts.Terrain.Height
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer
/-! adapted from Census/Coffer & Height/Highway -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration   Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler  Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}
    {E : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage} {f r b : Return.Wages}
    {q : UVNext.CouplingReset.ResetPrices} {η : ℕ → ℝ} {A : Scouts (F:=F)} {hL : ℕ→ℝ}
    {Q : Targets s K} {p : Expenses Q} {c c' : ℝ} (B : Directed G I Z K P) (R : Register D p f hL)
    {N m n : ℕ}

section hire
variable {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P}
def Scores (w:ℕ) (p : Q.Expense) (L:Side) (W μ c : ℝ) (o : ConnectedActivityE6.Target.Order G W) (x : ℝ) (j n : ℕ) (χ:Chi) :=
    grow G L x ^ w ≤ Real.exp (Q.ε*Pressure.Stores.till x) ∧
    ∀ (c' f : Side) (S : StepData c' f) (T : Tube G S), Works P L x S T → Stamp T→ ∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R) (Ω:ℕ→ℝ), (∀ i,1≤Ω i) → Sealed Ω R (2*incomingE G L x) →
      ∃ (C' d v t A b r B q i : ℝ) (k : ℕ), (∃ N: Captain H j C' d v t A b r B q k χ, Richer w Ω N.conduit) ∧ Armada Q L μ p.earn x i B j k ∧
        collars G i x j n * (salary Q L μ B x j k*(1-1/2)⁻¹) ≤ betaF G x L ^ p.wanting
lemma grange (w:ℕ) (Q : YM.ConnectedActivityE6.Target G P) (L : Side) : ∀ᶠ x in atTop, grow G L x ^ w ≤ Real.exp (Q.ε*Pressure.Stores.till x) := by
  have h:= (Rate.power (G:=G) (L:=L) (a:=3/8)).pow w|>.mul (Rate.cutoff Q.usable (a:=-(w:ℝ)-1))
  filter_upwards [h.below (by linarith only [Nat.cast_nonneg (α:=ℝ) w]) 1 zero_lt_one] with x hx
  apply le_of_mul_le_mul_right _ (Real.exp_pos (-Q.ε*Pressure.Stores.till x))
  rw [← Real.exp_add, neg_mul,add_neg_cancel,Real.exp_zero]; exact (le_abs_self _).trans (by simpa only [neg_mul,grow] using hx)
lemma housing (w:ℕ) (Q : YM.ConnectedActivityE6.Target G P) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense) (W μ c : ℝ) (o:Target.Order G W), 0<W → 0<μ →
    ∀ j n χ, ∀ᶠ x:ℝ in atTop, Scores w X L W μ c o x j n χ := by
  obtain ⟨m,hm⟩:= journeyman w P Q; refine ⟨m,fun L hL X W μ c o hW hμ j n χ=> ?_⟩
  by_cases he : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact (grange w Q L).mono fun x hx=>⟨hx,fun c f S T h=> (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim⟩
  obtain ⟨D,hd,hF,hX⟩:=he; obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:=hm L hL D hd j χ W hW μ hμ o
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j k hB
  filter_upwards [grange w Q L,H,hg n 0 X.wanting X.reach,hK] with x he' h hh hA
  refine ⟨he',fun c f S T hW hx R I Ω hΩ htΩ=>?_⟩
  simp only [pow_zero,mul_one] at hh
  exact ⟨C,_,_,_,_,_,_,_,_,_,_,h c f S T (hW.patch hF hX) hx R _ I Ω hΩ htΩ,hA,(le_abs_self _).trans hh⟩

lemma protracted (w:ℕ) (Q : YM.ConnectedActivityE6.Target G P) (L : Side) {μ : ℝ} (hm : 0<μ) : ∀ᶠ x in atTop,
    grow G L x ^ w ≤ Real.exp (Q.mark L μ x) := by
  let d x:= grow G L x; let g x:= Q.mark L μ x
  have hf : Rate G L (-(w:ℝ)-1) (fun x=> Real.exp (-g x)) := by
    apply (Rate.monitor_cutoff (show 0<μ/4 by linarith) (show (0:ℝ)<2 by norm_num)).congr
    apply Eventually.of_forall; intro x
    dsimp only; rw [Real.rpow_two]; unfold g; change Real.exp (- Delay.hatWin G L _ _ x)=_; unfold Delay.hatWin; congr 1; ring
  have hx := (Rate.power (G:=G) (L:=L) (a:=3/8)).pow w|>.mul hf
  filter_upwards [hx.below (by linarith only [Nat.cast_nonneg (α:=ℝ) w]) 1 zero_lt_one] with x h
  suffices hs : d x^w/Real.exp (g x) ≤ 1 from (div_le_one (Real.exp_pos _)).1 hs
  rw [div_eq_mul_inv, ← Real.exp_neg]; exact (le_abs_self _).trans h


end hire
end YM.PhysicalNext.Repeat.Height

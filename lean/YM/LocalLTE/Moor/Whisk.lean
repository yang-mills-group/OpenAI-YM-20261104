import YM.LocalLTE.Moor.Replica
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir
/-! Local LTE propagation: parameterized extension of Trio/Tir. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F:Side} {J₀ j i m n W w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side} (V:Config G c)
section lo
variable {S:StepData c f} {K₀:Teller G} {d p a U T' : ℝ} {X: ConnectedActivityE6.Target G K₀} {o: Target.Order G p} {L:Side} {T:Tube G S} {R R': RG.Rep G f}
   {Z : Cash p d a L X o T' T R} {Z':Cash p d a L X o T' T R'}
    (Wt : Match.Alliance Z' Z 1 0) (γ:ℝ) (n:ℕ) (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa: ∀ i:Stars,Offer G (Y i))
    (u:Site c)
local notation "P" => (B)
local notation "P₀" => (Beam.marquee Z' B)
local notation "O" => Chi.canonical
local notation "h₀" => (plusone Z' Wt O γ)
local notation "h₁" => (Meadow.timbresN (J₀:=J₀) Wt (χ:=O) γ n)
local notation "R₀" => (Meadow.panelN Z' J₀ n)
local notation "D₀" => Meadow.studioN J₀ X.halo (radiusB d)
local notation "f₀" => (Meadow.baronyN Z J₀ O n γ)
variable {sf c' : ℝ} (h : Collection.Local (posting B Z') B (plusone Z' Wt Chi.canonical γ) sf c') (hV : B.B=Pressure.radiusB d)
include h hV
lemma whiskN : ‖Trio.earnedN B Wt γ n J₀ u V‖ ≤ (ballCost D₀:ℝ)*sf:= by
  obtain ⟨a,ha,hX⟩:= h.cheap
  let Z:= B; let P':= posting B Z'; let f i:= masked B.threshold (P'.reg i).support (((P₀).read (plusone Z' Wt O γ)).E i) V
  let R i:= Meadow.garnerAt Z' B u i; have hv i : ((P₀).read h₀|>.regularOccurrence B i V)= f i:= by change masked _ ((P₀).reg i).support _ _=_; rw [Beam.rewrite_rule]
  unfold Trio.earnedN; simp_rw [hv]; apply le_trans (norm_sum_le ..)
  let s:= neighbors D₀ u; let E i x:= if (P'.reg i).site=x then a i * Real.exp (preExponent B * coverNumber B.B (P'.reg i).support) else 0
  calc
    _ ≤ ∑ i∈ R₀, ∑ x∈s,E i x:= by
        apply sum_le_sum; intro i hi; have hp : 0≤∑ x∈s,E i x:=sum_nonneg fun x _=> (hX x).1 i
        change ‖R i*f i‖ ≤ _; by_cases ht:R i=0; · rw [ht,zero_mul,norm_zero]; exact hp
        have he:= (Meadow.assignedN Z' B u i hi hV ht).2; rw [Beam.rewrite_rule] at he
        rw [norm_mul, Real.norm_of_nonneg (Meadow.nonnegative ..)]; apply (mul_le_of_le_one_left (norm_nonneg (f i)) (Meadow.portions ..)).trans; apply (CouplingShape.mask_cost (ha i) V).trans
        apply (le_mul_of_one_le_right (ha i|>.1) (Real.one_le_exp (show 0≤preExponent B * coverNumber B.B (P'.reg i).support from mul_nonneg (Song.headline B).exponent_pos.le (Nat.cast_nonneg _)))).trans;
        unfold E; rw [sum_ite_eq,if_pos (he (P'.reg i).anchor)]
    _ ≤ (ballCost D₀:ℝ)*sf:= by
        rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=> budget_sum (hX x) R₀))
        rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) h.H_nonneg
variable (ha :Wt.units=Equiv.refl _) (hh:Z'.supportP=Z.supportP) (hr:R'.path=R.path)
include ha hh hr
lemma skinN (hU: flags B.threshold V=∅): ‖f₀ u V‖ ≤ (ballCost D₀:ℝ)*sf:= by
  have he i : ((P₀).read h₀|>.regularOccurrence B i V)=((h₀).logRead i) V:= masked_eq _ _ _ _ (by unfold Healthy; rw [hU]; simp)
  have hp:= Trio.whiskN (J₀:=J₀) B V Wt γ n u h hV; unfold Trio.earnedN at hp; simp_rw [he] at hp
  rw [(Meadow.asterN O B Wt hr hh ha γ n u), Finset.sum_apply]; exact hp
lemma augustN (f : Stars→ℝ) (hq:∀ i (V:Config G (Y i)), flags B.threshold V=∅→∀ x, ‖fa i x V‖ ≤ f i) (hp:w+4 ≤ z) : ‖insightN B Wt γ n Q z fa J₀ u V‖ ≤ (ballCost D₀:ℝ)*sf +(ballCost D₀:ℝ)*sf +∑ i:Stars,|ray i| * ((Fintype.card (Site (Y i)):ℝ)*(f i+f i)) := by
  apply (norm_sub_le ..).trans; apply add_le_add ?_ (Trio.stipends B V Q z fa _ hq hp u)
  exact (norm_sub_le ..).trans (add_le_add (Trio.whiskN (J₀:=J₀) B V _ γ n _ h hV) (skinN B 1 Wt γ n u h hV ha hh hr (smoky («P»:=B) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using B.threshold_pos))))
end lo
end YM.PhysicalNext.Repeat.Trio

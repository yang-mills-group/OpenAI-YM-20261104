import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Income
import YM.LocalLTE.Tier.Crest
/-!
# Purchase inheritance comparison and principal interaction E

Height expenditure to be charged *additionally*, not twice against polygon.
All for exterior flags and actual covariance comparison with `Scratch` Π receipt.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt   
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm.Solo Clockwork
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {v w t : Return.Wages} {C : Programs s} {Q : Targets s K} {E : Expenses Q}
    {M : ℕ→ℕ→Record} {m : ℕ→ℕ→ℕ} {u a : ℕ→ℝ} {D : Rolls s} {W : ℝ} {c : ℝ}

section tar
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {L : Side} {x : ℝ} {n : ℕ}
-- Invoiced actual asks Plateau.
def VergeT (Q : ConnectedActivityE6.Target G P) (o : ConnectedActivityE6.Target.Order G W) (M : Record) (C : Libretto G n) (ε v : ℝ) (m p : ℕ) (κ : Chi) (L : Side) (x c₀ : ℝ) : Prop :=
  ∀ {c f : Side} {S : StepData c f} (T : Tube G S), Works P L x S T →
    ∀ (R : RG.Rep G f) (μ α : ℝ) (H : Cash W x μ L Q o α T R) (B : BudgetPoint),
    B.B=radiusB x → B.power=p → Plays C M B R.p P T x → Q.halo+ 5 ≤ m → Release.accepts m R.p.supportExponent ε L → Release.Quotation C p m R.p.supportExponent ε v →
    Lute.Plented C M B R.p L m x (gStep R.beta)→ ∀ j≥n, ∀ (C' d h Y A b r B₀ q : ℝ) (k : ℕ), Captain H j C' d h Y A b r B₀ q k Chi.canonical → ∀ q ε' F' ξ, Pumps R F' ξ → Brim.Hauses F' H M q κ Chi.canonical ε' B ε (c₀*ξ) (c₀*ξ)

lemma tapesT (G : Gauge) (hG : G.Simple) (P : Teller G) (Q : ConnectedActivityE6.Target G P) (p L) {n : ℕ} (M : Record) (C : Libretto G n) (W c ε v : ℝ) (o : ConnectedActivityE6.Target.Order G W) (m : ℕ) (κ : Chi)
    (hn : 2 ≤ n) (hM : M.ε≤1/4) (hc : 0<c) (ht : v / (L:Side).val ≤ c) (he : 0 ≤ ε) : ∀ᶠ s in atTop, VergeT Q o M C ε v m p κ L s c := by
  by_cases h : ∃ t : Patch,t.L=L ∧ t.J=P.j ∧ t.Branches P.bind G
  swap; · exact Eventually.of_forall fun s c f S T hh=> (h ⟨S.patch,hh.length_eq,hh.funds.atStep,hh.funds.kernel⟩).elim
  obtain ⟨D,h,hF,h'⟩:= h
  obtain ⟨X,hX,H⟩:= Brim.pressTier G hG P L D h' p n C M hM hn Chi.canonical κ W o ε m he
  filter_upwards [eventually_gt_atTop (0:ℝ),H,hX.below (by norm_num) _ hc] with x hx hh hE c' f S T hs R μ α H B hb hp hW hA hf hh' hu j hj C' d v' Y A b r B₀ q k N q' ε' F' ξ HG
  obtain ⟨⟨z,hz,hZ⟩,z',hz',hZ'⟩:=hh c' f S T (hs.patch h hF) hs R Q μ α H B hb hp hW hA v hf hh' hu _ hj A b d Y C' B₀ r v' q k N q' ε' ξ F' HG -- field order!
  obtain ⟨-,_,_,hc'⟩:= HG
  have hp:= budget_nonneg (hc' 0)
  exact ⟨⟨z,hz, fun i=>budget_loosen (hZ i) (mul_le_mul_of_nonneg_right ht hp)⟩,
    z',fun i=>budget_loosen (hz' i) (mul_le_mul_of_nonneg_right hE hp),hZ'⟩
end tar

variable (Y : Register D E w a) {Θ : Protection D} (C M v t m) (κ : ℕ→ℕ→Chi)
def PewT (W : Delays Θ) (c : ℕ→ℕ→ℝ) := ∀ j x,W.betaEntry j ≤ x → ∀ i,StepStages j i → s.first ≤ i → VergeT (Q j i) (Y.o j i) (M j i) (C j i) (raise t j i) (v j i) (m j i) (s.profile i).power (κ j i) (D.L j) x (c j i)

lemma pewsT (hG : G.Simple) (c : ℕ →ℕ→ℝ) (hc : ∀ i j,0<c i j) (hy : ∀ i j, StepStages j i → v j i / (D.L j).val ≤ (c j i)) (hM : ∀ j i,StepStages j i → s.first ≤ i → (M j i).ε ≤ 1/4) (ht : ∀ j i,0≤t j i) (V : Delays Θ) :
    ∃ W : Delays Θ, DelayLe V W ∧ ∀ X : Delays Θ, DelayLe W X → PewT v t C M m Y κ X c := by
  have he j i (h : StepStages j i) : ∀ᶠ x in atTop, s.first ≤ i → VergeT (Q j i) (Y.o j i) (M j i) (C j i) (raise t j i) (v j i) (m j i) (s.profile i).power (κ j i) (D.L j) x (c j i) := by
    by_cases he : s.first ≤ i
    · filter_upwards [tapesT G hG _ (Q j i) (s.profile i).power (D.L j) (M j i) (C j i) _ _ _ (v j i) (Y.o j i) (m j i) (κ j i) (le_trans (by decide) (s.profile i).order_ge) (hM j i h he) (hc ..) (hy i j h) (add_nonneg (ht j i) zero_le_two)] with x hx h₁; exact hx
    simp [he]
  obtain ⟨X,-,hv,hx⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (he j)); exact ⟨{V with betaEntry:=X},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun _ h j x hx'=> hx _ x ((h.beta _).trans hx')⟩
end YM.PhysicalNext.Repeat.Roof

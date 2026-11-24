import YM.RG01Estimate.Pruned
import YM.RG01Estimate.CensusStep
import YM.UVExtension.Guild.Chair

/-!
# The pre and post reservations needed for the second pruning

CURRENT pair with genuine stage changes, pre-L threshold first. Includes epsilon for the
endpoint error. Keep it on the constructor: communicate all exponents before it pays
recent delays. Auxiliary tori must pay the same size thresholds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate
open Function Filter Set Lattice RG Pressure Wilson Pressure.Stores Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes UVNext Extra.Iteration Meadow
open PriceCompiler Org Input Supply Pressure.Testing Time
open Roost Opera
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Expense Reprice
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
namespace Activation
-- generic post-L arithmetic
include G in
lemma compare_rates (L : Side) (X : RG.Stage) (r : ℕ) (hr : 2≤r) : ∀ᶠ s in atTop,
    let t:= Fate.target r G L s
    Height.away X*(t+t+t) ≤ betaF G s L ^ (-Fate.aim r-(1/64:ℝ)) ∧ Fate.debt r G L s ≤ incomingE G L s := by
  let p:= Fate.aim r; let w:= p+1/64
  have ht : Rate G L (Fate.spruce r) (Fate.target r G L) := Rate.power
  have hv : Fate.spruce r < -p-(1/64:ℝ):= by unfold Fate.spruce p; linarith only
  have hk : (2:ℝ) ≤ r := by exact_mod_cast hr
  filter_upwards [(((ht.add ht).add ht).mul_left (Height.away X)) _ hv,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hh hx
  refine ⟨(le_abs_self _).trans hh,?_⟩
  unfold Fate.debt
  have hs : incomingE G L x=betaF G x L^(-(11/10):ℝ) := by
    unfold incomingE
    rw [Real.sqrt_eq_rpow,← Real.rpow_neg (zero_le_one.trans hx),← Real.rpow_mul (zero_le_one.trans hx)]; norm_num
  rw [hs]; apply Real.rpow_le_rpow_of_exponent_le hx; unfold Fate.tender Fate.aim; push_cast; linarith only [hk]

lemma path_requests (G : Gauge) (L : Side) (X : RG.Stage) (U v : ℝ) (hu : 0<U) : ∀ᶠ s in atTop,
    ∀ p:BudgetPoint,p.threshold ≤ 2*Pressure.fiery G s L → p.power=X.power → p.order=X.order → p.supportExponent=X.supportExponent→ p.B= radiusB s →
    ∀ (β b Λ : ℝ), |β| ≤ 2*betaF G s L → |b| ≤ U → 0≤Λ → Λ ≤ ConnectedActivityE6.loopBill G L s →
      Real.exp (-(X.width/4)*p.B)*Song.octaveNeed G p X.clip X.width X.paths Λ β b ≤ betaF G s L ^ v ∧
        preExponent p / p.B ≤ X.width/4 := by
  have hp : Rate G L v (fun x=> Real.exp (-(X.width/4)*radiusB x)) := by
    apply (Rate.cutoff (G:=G) (L:=L) (a:=v) (show 0<X.width/4 from div_pos X.width_pos (by norm_num))).compare
    apply Eventually.of_forall; intro x; rw [abs_of_nonneg (Real.exp_pos _).le,abs_of_nonneg (Real.exp_pos _).le]; apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (show (till x:ℝ)≤radiusB x from (by exact_mod_cast Nat.div_le_self ..)) (by have he:=X.width_pos; linarith)
  filter_upwards [Meadow.flights G L X U hu,(hp.mul (Rate.power (a:=-(7/16)))) v (by linarith only)] with x hx ht p he hf hO hY hB β b Λ h hU hL hΛ
  obtain ⟨hb,_,hv⟩:= hx p he hf hO hY hB β b Λ h hU hL hΛ
  refine ⟨?_,hv⟩; nth_rw 1 [hB]; exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans ((le_abs_self _).trans ht)

section pre
variable {s : Sheet G} {K : MapPrices} (X : Targets s K)
def Before (u : ℕ→ℕ) :=
    ∀ j i, StepStages j i → ∀ L : Side, u j ≤ L.val →
    let S:= s.profile i
    ∀ W μ a:ℝ, 0<W → 0<μ → 0≤a → a < (X j i).exp → ∀ o : Target.Order G W, ∀ r, 2≤r →
      ∀ᶠ x : ℝ in atTop, Fate.Admission (X j i) L W μ a o S.order S.power r Chi.canonical x
lemma preprice (h : ∀ i j, (X j i).rate + 3/8 < 0) : ∃ u, Before X u := by
  choose u hu using fun j i=> Fate.admit_stage (X j i) (h ..)
  refine ⟨fromMax u,fun j i hx L hk=> ?_⟩
  intro S W μ a hw hμ ha ht o r hr
  exact hu j i L ((le_fromMax u hx).trans hk) W μ a hw hμ ha ht o S.order S.power r hr Chi.canonical
variable {X} {M : Expenses X} {w : Return.Wages} {C : Programs s} {D : Rolls s} {Z : Protection D}
variable (Y : ℕ→ℕ→JointLoad.Heir.Record) {v:ℕ→ℝ} (Q:PhysicalNext.Repeat.Register D M w v) (u : Return.Wages) (b : ℕ→ℕ→ℕ)
-- values u,t from Roost; reserve t_facet and stronger Wν. output grows exponent noted.
def glyph (G:Gauge) (L:Side) (x:ℝ):ℝ:= betaF G x L ^ (-(1/4):ℝ)
def ready (C : Programs s) (i j r:ℕ) (x:ℝ) :=
    let A:= s.profile i; let L:= D.L j
    Fate.Admission (X j i) L (w j i) (Q.μ j i) (M j i).earn (Q.o j i) A.order A.power r Chi.canonical x ∧
      (∃ d:ℝ, 0 ≤ d ∧ Height.away A*d ≤ glyph G L x ∧ Single.Gate G (Testing.query s K j i) L A.power A.order (C j i)
        (Y j i) Chi.canonical (w j i) (Q.o j i) (Solo.raise u j i) (b j i) d x) ∧
      (∀ p:BudgetPoint,p.threshold ≤ 2*Pressure.fiery G x L→p.power=A.power→p.order=A.order→p.supportExponent=A.supportExponent→p.B= radiusB x→∀ β k Λ,|β| ≤ 2*betaF G x L→|k| ≤ (s.profile j).drift + |G.slopeConstant*Real.log (D.L j).val| + 1→0≤Λ→Λ ≤ ConnectedActivityE6.loopBill G L x →
       Real.exp (-(A.width/4)*p.B)*Song.octaveNeed G p A.clip A.width A.paths Λ β k ≤ Fate.target r G L x ∧ preExponent p / p.B ≤ A.width/4) ∧
      (let t:= Fate.target r G L x
       Height.away A * (t+t+t) ≤ betaF G x L ^ (-Fate.aim r-(1/64:ℝ)) ∧ Fate.debt r G L x ≤ incomingE G L x) ∧ Real.exp 1 ≤ x
variable (C : Programs s) (g:G.Simple)
include g
lemma around {t:ℕ→ℕ} (i j r:ℕ) (h : StepStages j i) (hp:2≤r) (hu: 0≤Solo.raise u j i)
    (hk : Before X t) (ht:t j ≤ (D.L j).val) (hY : (Y j i).ε≤1/4): ∀ᶠ x in atTop, ready Y Q u b C i j r x := by
  let A:= s.profile i; let L:=D.L j; let w':=(s.profile j).drift+|G.slopeConstant*Real.log (D.L j).val|+1
  let P:=Testing.query s K j i
  let T:=M j i
  have hh : 2≤A.order:= (show 2≤6 by decide).trans A.order_ge
  have hy:0<w':= by unfold w'; linarith only [(s.profile j).drift_ge,abs_nonneg (G.slopeConstant*Real.log (D.L j).val)]
  have hM:= (hk j i h L ht (w j i) (Q.μ j i) T.earn (Q.consumes j i h).1 (Q.consumes j i h).2.1 T.price (by linarith only [T.worth,T.first,T.second]) (Q.o j i) r hp)
  have hv: ∀ᶠ x:ℝ in atTop, ∃ d:ℝ, 0≤d ∧ Height.away A*d ≤ glyph G L x ∧ Single.Gate G P L A.power A.order (C j i)
      (Y j i) Chi.canonical (w j i) (Q.o j i) (Solo.raise u j i) (b j i) d x:= by
    by_cases he:∃ D:Patch,D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
    swap
    · filter_upwards [Delay.shift_pos G L] with x hx
      refine ⟨0,le_rfl,by rw [mul_zero]; unfold glyph; positivity, fun _ _ S T h=>False.elim (he ⟨S.patch,h.length_eq,h.funds.atStep,h.funds.kernel⟩)⟩
    obtain ⟨k,p,h',hs⟩:= he
    obtain ⟨f,hf,H⟩:= Single.bystage G g P L k hs _ _ (C j i) (Y j i) hY hh Chi.canonical Chi.canonical (w j i) (Q.o j i) _ (b j i) hu p h'
    filter_upwards [H, ((Brim.absolut hf).mul_left (Height.away A)) (- (1/4)) (by norm_num)] with x hx hr
    exact ⟨|f x|, abs_nonneg _, (le_abs_self _).trans hr,hx⟩
  filter_upwards [hM,hv,path_requests G L A w' (Fate.spruce r) hy, compare_rates (G:=G) L A r hp,eventually_ge_atTop (Real.exp 1)] with x hx hu hh hk hN
  exact ⟨hx,hu,hh,hk,hN⟩

/-- Activation at each stage J. all r up to J. Can (separately) make room for
support and perturbative packet purchases before finally choosing V. -/
def OnTrack (V : Delays Z) := ∀ j x, V.betaEntry j ≤ x → ∀ i, StepStages j i → s.first ≤ i → ∀ r,
    2 ≤ r → r ≤ j → ready Y Q u b C i j r x

lemma activate {t:ℕ→ℕ} (hu: ∀ j i, StepStages j i → 0≤ Solo.raise u j i)
    (hk : Before X t) (ht:∀ j,t j ≤ (D.L j).val) (hY: ∀ j i, StepStages j i → s.first ≤ i → (Y j i).ε≤1/4) (V:Delays Z):
    ∃ W:Delays Z, DelayLe V W ∧ ∀ Z', DelayLe W Z' → OnTrack Y Q u b C Z' := by
  have he j i (h:StepStages j i):∀ᶠ x in atTop, s.first ≤ i → ∀ r, 2 ≤ r → r ≤ j → ready Y Q u b C i j r x:= by
    by_cases hh:s.first ≤ i
    swap
    · exact Eventually.of_forall fun _ hk=> (hh hk).elim
    filter_upwards [(eventually_all_finset (Finset.Icc 2 j)).mpr (fun r hr=> around Y Q u b C g i j r h (Finset.mem_Icc.mp hr).1 (hu j i h) hk (ht _) (hY j i h hh))] with i hi X r hv hl
    exact hi r (Finset.mem_Icc.mpr ⟨hv,hl⟩)
  obtain ⟨x,-,hx,hP⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (he j))
  exact ⟨{V with betaEntry:=x}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ h j y hv=> hP j y ((h.beta _).trans hv)⟩
end pre
end Activation
end YM.RG01Estimate

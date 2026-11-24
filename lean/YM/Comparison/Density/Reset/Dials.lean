import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.Comparison.Density.Convert.Report

/-!
Kinetic port. Extract ONLY remaining vacuum E's affine data. Can even
supply leftover term family with some calibration input. No retuning here
on a desired trajectory. Exact flags still at `P.p`. Careful about kinetic
includes WHOLE nonlinear canonical cubic/quartic/base average including
kept/clipping. Only when `P.path` is actually the stipulated rendering with
bounds do we get this theorem. Model Z regular terms NOT extracted (should
be put in affine-null format, choose that in formal model; this is not
identifying beta along different trajectories). Output beta here temporary.
Uses accepted VerifiedReset atlas lemmas on our E family alone. Does
not drop any marked label.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Reset
open Fusing Markers Testing Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo UVNext.CouplingReset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

section Coupons
variable {n : Side} {G : Gauge} {p : BudgetPoint} {e c : ℝ} {A : Activities G n}
lemma expandE (h : 0≤e) (hq : 0≤ e+3) : later p (e+3) hq = later (later p e h) 3 (by norm_num) := by
  simp [later, ← add_assoc]
lemma expandF (h : 0≤e) (hq : 0≤ e+1) : later p (e+1) hq = later (later p e h) 1 (by norm_num) := by
  simp [later, ← add_assoc]
lemma affordable (h : 0≤ e) (hq : 0 ≤ e+3) (he : A.EBound (later p (e+3) hq) c) :
    ∃ u, (∀ i, (later p e h).supBounds (A.reg i).site (A.reg i).support (A.E i) (u i)) ∧ Quotes.early (later p e h) A.reg u c := by
  rw [expandE h] at he; obtain ⟨u,hu,he⟩:=he
  refine ⟨_,hu,fun x=>?_⟩
  convert he x using 2 with i; unfold BudgetPoint.mass; split_ifs; exact mul_comm ..; rfl
lemma admissible (h : 0≤ e) (hq : 0≤ e+1) (he : A.KBound (later p (e+1) hq) c) :
    ∃ u, (∀ i, 0 ≤ u i ∧ ∀ U, ‖A.K i U‖ ≤ u i) ∧ Ac.Hit (fun i => (A.forced i).support) (later p e h).B u ((later p e h).supportExponent+1) c := by
  rw [expandF h] at he; obtain ⟨u,hu,he⟩:=he
  refine ⟨_,hu,fun x=>?_⟩
  convert he x using 2 with i; unfold BudgetPoint.mass; split_ifs; exact mul_comm ..; rfl
lemma weave_family {P Q : Activities G n} (h : P.RegularFamily p) (ha : Q.RegularFamily p):
    (weave P Q).RegularFamily p := by
  refine ⟨weave_art h.smooth ha.smooth, fun i=>?_,fun i =>?_⟩
  · dsimp [weave]; cases rubric i; exact h.at_flat _; exact ha.at_flat _
  dsimp [weave]; cases rubric i; exact h.vanish _; exact ha.vanish _
end Coupons

-- P.reg model and E given as direct sum by hypothesis to assign
-- signed comparison. Use A.path as MODEL path precisely carried.
variable {n : Side} {G : Gauge}

protected def book (A : Activities G n) (P : Rep G n) : Listing G n := ⟨A.reg,P.activities.forced⟩
def ant (A : Activities G n) (P : Rep G n) : Collection.Source G n:= ⟨A.E,P.activities.K⟩
def sewn (A : Activities G n) (P : Rep G n) := (Reset.book A P).read (ant A P)
def dip (A : Activities G n) (P : Rep G n) := shelves (Reset.book A P) P.path P.p
def trade (A : Activities G n) (P : Rep G n) := branch (Reset.book A P) P.path P.clip P.p (ant A P) 0
def net (A : Activities G n) (P : Rep G n) := Pipes.pours (dip A P) (trade A P)
def exitPath (A : Activities G n) (P : Rep G n) (M : Activities G n): Rep G n:=
    {P with activities:=weave M (net A P), beta:=P.beta+delta A, v:= vac (ant A P) P.v}

variable {P : Rep G n} {A M : Activities G n} {e b p a σ C Λ : ℝ}

def planMove {s x} (h : A.Moves s x) (hP : P.activities.Moves s x):
    (sewn A P).Moves s x:= ⟨h.ep,hP.kp,h.reg_site,h.reg_support,hP.forced_support,hP.forced_inventory,
      hP.forced_tests,h.valuesE,hP.valuesK⟩
structure Panel (M A : Activities G n) (P : Rep G n) (e b a c σ C Λ : ℝ): Prop where
  growth : 0≤e
  leaves : P.activities.reg=(weave M A).reg
  under : P.activities.E=(weave M A).E
  rotates s x : Nonempty (P.activities.Moves s x)
  ancillary : Art A P.p
  works s x : Nonempty (A.Moves s x)
  modelMoves s x : Nonempty (M.Moves s x)
  model : M.RegularFamily P.p
  lesser : M.EBound (later P.p e growth) c
  loanE : A.EBound (later P.p (e+3) (by linarith [growth])) a
  forces : P.activities.ForcedFamily P.p
  loanK : P.activities.KBound (later P.p (e+1) (by linarith [growth])) b
  enough : 20<n.val
  width : Width (later P.p e growth) P.clip σ
  safe : Decent P.clip (later P.p e growth)
  angles : P.path.Bounds P.clip σ C Λ
namespace Panel

variable {c : ℝ} (g : G.Simple) (h : Panel M A P e b a c σ C Λ)

include h
lemma travels : Collection.Local (Reset.book A P) (later P.p e h.growth) (ant A P) a b:= by
  have hf:=h.forces
  exact ⟨fun i=> let ⟨hp,hs,hb,hx,hg⟩ := h.ancillary i; ⟨hp,hs,hb,hx,hg⟩,⟨hf.sym,hf.symtest,hf.meas,hf.meas_test,hf.reads,hf.reads_test,hf.permit⟩,
    fun s b=> ⟨planMove ((h.works s b).some) ((h.rotates s b).some)⟩,
    affordable h.growth _ h.loanE, admissible h.growth _ h.loanK⟩
include g
lemma projection : P.p.threshold^2*|delta A|≤a:= by
  have he:= delta_bound g h.travels.projects; exact he
lemma ramp : Payments.Fittings (trade A P) (dip A P) (later P.p e h.growth):= h.travels.fittings g h.angles h.safe h.enough _ (delta A)
lemma regular : (net A P).RegularFamily P.p := by
  have hr:= (ramp g h).regular; exact ⟨fun i=> let ⟨hp,hs,hb,hx,hg⟩:= hr.smooth i; ⟨hp,hs,hb,hx,hg⟩,hr.at_flat,hr.vanish⟩
lemma listed : (net A P).EBound (later P.p e h.growth) (regularNeed G (later P.p e h.growth) P.clip σ C 0 a) := by
  have hh:=h.travels; obtain ⟨u,hu,hb⟩:=hh.cheap
  let B:=later P.p e h.growth
  obtain ⟨he,-⟩:= Local.quote_family h.angles h.safe h.width 0 _ hu hb (delta_bound g hh.projects)
  have hm (i) := Local.quote_regular g h.angles h.safe 0 (delta A) hu hh.smooth i
  exact ⟨_,fun i=> hm (numbering _ i),fun x=> Cost.equiv (numbering _) (he x)⟩
lemma reset_terms (U : Config G n) : P.exponent U=(exitPath A P M).exponent U+∑' i,(trade A P).logarithm i U := by
  have hj:= h.travels.exponent g h.angles h.safe h.width 0 h.enough P.beta P.v U
  rw [add_zero,zero_mul,sub_zero] at hj
  have he := Convert.plain h.growth h.lesser; unfold Rep.exponent
  have ht : P.activities.additive P.p U=(weave M A).additive P.p U := by simp only [Activities.additive, Activities.regularOccurrence,h.leaves,h.under]
  simp only [exitPath]; rw [ht,weave_summed he (Convert.plain _ h.loanE),weave_summed he (Convert.plain h.growth (listed g h))]
  change vac _ _ * _ - P.path.inChannels P.clip _ _ U - (net A P).additive P.p U + _ = P.v * _ - _ - A.additive P.p U at hj
  change vac _ _ * _ - P.path.inChannels P.clip P.p (P.beta+delta A) U - _ + ∑' i,(trade A P).logarithm i U=
      _ - P.path.inChannels P.clip P.p P.beta U - _ at hj
  linarith
lemma scalar : |(exitPath A P M).v-P.v| ≤ a := by
  have hh:= h.travels
  let Y:= (1:Config G n)
  -- sum site by site
  have hZ := (Local.raw_sum g hh Y).1
  let f (x:Site n) i := if (A.reg i).site=x then A.E i Y else 0
  have hp : Summable (fun i=> A.E i Y):= hZ
  have hs x : Summable (f x) := Summable.of_norm_bounded hp.norm (fun i => by unfold f; split <;> simp)
  obtain ⟨u,hu,hb⟩:= Convert.plain _ h.loanE
  have hv x : ‖∑' i,f x i‖ ≤ a:= by
    refine (norm_tsum_le_tsum_norm (hs x).norm).trans (((hs x).norm.tsum_le_tsum (fun i=> ?_) (hb x).2.1).trans (hb x).2.2)
    unfold f; split_ifs
    · exact ((hu i).2 1 (flat_ok ..) [] (by simp) (by simp)).trans (P.p.loMass _ _ (hu i).1)
    simp
  have ha i : A.E i Y=∑ x, f x i:= by simp [f]
  change |P.v-(∑' i,A.E i Y)/sites n-P.v|≤a
  rw [show P.v - _ - P.v= -((∑' i,A.E i Y)/sites n) by ring, abs_neg,abs_div,abs_of_pos (sites_pos n),div_le_iff₀ (sites_pos n)]
  rw [show (fun i=> A.E i Y) = fun i=> ∑ x, f x i from funext ha, Summable.tsum_finsetSum fun x _=>hs x]
  exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun x _=>hv x)).trans_eq (by simp [UVNext.CouplingReset.sites,mul_comm a]))
end Panel
end YM.Comparison.Density.Reset

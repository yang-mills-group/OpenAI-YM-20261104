import YM.GapsContact.Jost.Bridge
import YM.GapsContact.Series.Probe
/-!
# Actual real-time propagation using the log-running coupling and this analysis
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Craft
open Function Filter Set MeasureTheory Metric Boundary Analysis Tunnel Jost Ascent EveryPhase
open Pattern Work.C20 Spec Next.BOUNDARY Trace Trace.Pilot Trace.Terrace
open scoped Topology BigOperators ContDiff InnerProductSpace Classical
universe u
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F : Final C f S){hG:G.Simple}
variable {n :ℕ} {g:ℝ→ℝ} (hg: Coupling G g)

-- no smoothness or monotonicity of g used. Only running.
abbrev Index := ℝ × Survey F
def focus (F : Final C f S) : Filter (Index F) := trail ×ˢ Filter.principal univ
abbrev metric (g:ℝ→ℝ)(x:Index F):= g x.1
lemma horizon {P:Index F→ Prop}: (∀ᶠ x in focus F,P x) ↔ ∀ᶠ r in trail,∀ i:Survey F,P (r,i):=by rw [focus,eventually_prod_principal_iff]; simp
lemma smiling : ∀ᶠ i in focus F, 0 < i.1 :=(horizon F).2 (Eventually.mono self_mem_nhdsWithin fun _ ht _=>ht)
lemma walk : Tendsto Prod.fst (focus F) trail := tendsto_fst
include hg hG
lemma train : Nonempty (Meter (focus F) (metric F g)):=by
   let v(k:ℕ):= Real.exp (-(Pattern.wage k ^2)⁻¹); let b(k:ℕ): Index F:= (v k,none); let Z:= G.slopeConstant⁻¹
   have ht:0<Z:= inv_pos.mpr (Gauge.slopeConstant_pos hG)
   have hv: Tendsto v atTop trail:=by
      apply tendsto_nhdsWithin_iff.mpr; refine ⟨?_, Eventually.of_forall fun i=> Real.exp_pos _⟩
      apply Real.tendsto_exp_atBot.comp
      apply tendsto_neg_atTop_atBot.comp
      apply tendsto_inv_nhdsGT_zero.comp; exact tendsto_nhdsWithin_iff.mpr ⟨by simpa using Pattern.wage_limit.pow 2,Eventually.of_forall fun i => pow_pos (wage_pos i) 2⟩
   have he:Tendsto b atTop (focus F) := hv.prodMk (tendsto_principal.mpr (Eventually.of_forall fun _=> Set.mem_univ _)) -- filter product lemma?
   refine ⟨⟨b,he,Real.sqrt Z,Real.sqrt_pos_of_pos ht,?_, (hg.conforms hG).comp (walk F), (walk F).eventually hg.positive⟩⟩
   apply ((hg.running.comp hv).sqrt).congr'; filter_upwards [hv.eventually hg.positive] with i hi
   have hw(i): LogV (v i)= (Pattern.wage i^2)⁻¹:=by simp [LogV,v]
   change Real.sqrt (LogV (v i)*g (v i)^2)= g (v i)/Pattern.wage i
   have hp:= Pattern.wage_pos i
   rw [hw, Real.sqrt_mul (by positivity),Real.sqrt_inv,Real.sqrt_sq hp.le,Real.sqrt_sq (by exact hi.le),div_eq_inv_mul]

lemma converted (q:ℕ):∃ D:ℝ,0≤D ∧ ∀ᶠ r in trail, LogV r ^ q ≤ D*(g r)⁻¹^(2*q):=by
   let C:= G.slopeConstant⁻¹
   have hc:0<C:=by unfold C; have hh:=Gauge.slopeConstant_pos hG; positivity
   refine ⟨(2*C)^q, by positivity,?_⟩
   filter_upwards [hg.positive, hg.running.eventually_le_const (show C < 2*C by linarith), (Real.tendsto_log_atTop.comp (show Tendsto (fun x:ℝ=> x⁻¹) trail atTop from tendsto_inv_nhdsGT_zero)).eventually_ge_atTop 0] with r hr hx hh
   have hp : LogV r ≤ (2*C)*(g r)⁻¹^2:= by rw [inv_pow,← div_eq_mul_inv]; exact (le_div_iff₀ (pow_pos hr _)).mpr hx
   rw [pow_mul,← mul_pow]; exact pow_le_pow_left₀ hh hp _

variable {F} (L: Almanac F) {D:∀ _:Survey F,∀ n,Blanket n}
variable (X: ∀ i:Survey F,(Survey.reads L i).world.Aurora (D i))
variable {d:Fin n→ℕ}(v:∀ i:Fin n,ℝ→ S.Field (d i))

-- uniformity over phase (physical futures). X may be chosen arbitrarily, no
-- effect of frequency extensions on output.
def ink (r:ℝ)(i:Fin n) := S.pin _ (v i r)
def ship (i:Index F):= weather (X i.2) (ink v i.1) i.1

def eu (S:Table C.book)(F:Final C f S)(v:∀ i:Fin n,ℝ→ S.Field (d i))(i: Index F) (p:Points n):= S.classMoment (Survey.table i.2) d (i.1 • p) (fun j=> v j i.1)
local notation "M" => wickSlice n
omit hg hG
lemma truth (i:Index F)(hr:0 < i.1) {x:Points n}(hx:x∈ordered n) : eu S F v i x=ship L X v i (wickSlice n x):=by
   unfold ship weather; rw [Complex.coe_smul,← map_smul]
   have hp:i.1 • x∈ ordered n:=by
       change readings (i.1 • x)∈ east n; exact east_up (readings x) hx i.1 hr
   exact (emit_root (Survey.fits L i.2).fromPhase.heat (observe L i.2 (X i.2)).2 (fun j => (⟨d j,v j i.1⟩: S.Tag)) hp).symm
lemma ship_motion : ∀ᶠ i in focus F, AnalyticOnNhd ℂ (ship L X v i) (tube n) := (smiling F).mono fun i h=> hollow _ (observe L i.2 _).2 _ i.1 h

variable (hv:∀ i, Measured F (d i) (v i)) (Z:Roll.{u} F hG L)
include hG hv Z hg
lemma ship_expense : ∃ b:ℕ,Scoped (focus F) (ship L X v) (tube n) (fun i=> (metric F g i)⁻¹^b):=by
   obtain ⟨A,hA,k,h⟩:=Temperate.core Z v hv; refine ⟨2*k,fun K hK hx=>?_⟩
   obtain ⟨t,ht,hp,h₀⟩:= ((Room.compact hK hx).and ((show ∀ᶠ k:ℝ in trail,0<k from self_mem_nhdsWithin).and ((ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds))).exists
   obtain ⟨W,hW,hw⟩:=converted (hG:=hG) hg k; refine ⟨A*W*t⁻¹^k,by positivity,?_⟩; apply (horizon F).2; filter_upwards [hw,h] with r hr hR i x hx
   refine (hR.full i _ (X i) t ⟨hp,h₀⟩ x (ht x hx)).trans ?_
   change _ ≤ A*W*_*(g r)⁻¹^_; calc
      _ ≤ A*(W*(g r)⁻¹^(2*k))*t⁻¹^k:=by gcongr
      _ = _ :=by ring

omit hg hG hv Z in
lemma glimpse {Ω E T:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedSpace ℂ E][IsScalarTower ℝ ℂ E] [ProperSpace E]
     [NormedAddCommGroup T] [InnerProductSpace ℝ T] {u:Ω→T→ℂ}{A:Ω→E→ℂ}{k:Filter Ω}{s:Set E}{t:Set T} (hs:IsOpen s)(ht:IsOpen t)
     (M':T→L[ℝ] E)(hM:MapsTo M' t s){w:Ω→ℝ}(hw:∀ᶠ i in k,0<w i)(hA:∀ᶠ i in k, AnalyticOnNhd ℂ (A i) s)(hu:∀ᶠ i in k,EqOn (u i) (A i ∘ M') t)
     (hz: ∃ q:ℕ,Scoped k A s (fun i=>(w i)⁻¹^q)) : Breeze k w u t:=by
  let W(i:Ω)(x:T):=((fderiv ℂ (A i) (M' x)).restrictScalars ℝ).comp M'
  have he : ∀ᶠ i in k,∀ x∈ t, HasFDerivAt (u i) (W i x) x:=by
     filter_upwards [hu,hA] with i hi h x hx
     apply (((h _ (hM hx)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp _ M'.hasFDerivAt).congr_of_eventuallyEq
     filter_upwards [ht.mem_nhds hx] with y hy using hi hy
  refine ⟨he.mono fun i h x hx=> (h x hx).differentiableAt, fun K hk hK=>?_⟩
  obtain ⟨b,hB⟩:= hz; obtain ⟨C,hC,h⟩:= hB.diff (hw.mono fun i hi=> pow_nonneg (inv_pos.mpr hi).le _) hs hA _ (hk.image M'.continuous) (image_subset_iff.mpr (fun x hx=> hM (hK hx)))
  refine ⟨b,C*‖M'‖, mul_nonneg hC (norm_nonneg _),?_⟩
  filter_upwards [h,he] with i h hh x hx; rw [(hh x (hK hx)).fderiv]
  apply le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
  rw [ContinuousLinearMap.norm_restrictScalars, mul_right_comm C]; exact mul_le_mul_of_nonneg_right (h _ (mem_image_of_mem _ hx)) (norm_nonneg _)

include X in
lemma real_breeze :Pattern.Breeze (focus F) (metric F g) (eu S F v) (ordered n):= glimpse (south n) (ordered_open n) M wick_tube ((walk F).eventually hg.positive) (ship_motion L X v) ((smiling F).mono fun i hi _ hx=> truth L X v i hi hx) (ship_expense hg L X v hv Z)
end YM.GapsContact.Craft

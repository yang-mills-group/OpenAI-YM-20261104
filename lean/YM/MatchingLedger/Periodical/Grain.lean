import YM.MatchingLedger.Periodical.Piece

/-!
# The SD identity for actual conditional weights with the gate

For analytic test jet transfer: combine the large-volume exact weights, pack cost is retained
literally here before this integration. Full piece restricted to this chart test (even if the full law is
nonanalytic there, cut at strictly smaller angle for test). We pay for **undoing** the gate next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices) (hB:S.patch.Branches S.kernel G)
    (A : ChartRatio G) (Y : Chip (Page G c)) (U : F.Slice G)(t r : ℝ) (R : Support c) (i : Needle F G) (p : Poly (Needle F G))
local notation "I" => Sum.inl i
local notation "D" => depot F (Sum.inl i)

def juice (x:G.Color) :=
  let u:= slip F U i.1 x
  Real.exp (-(sat F s A t i (column F A Y R u)))
def word (x:G.Color) := run F A t p (slip F U i.1 x)
def caseCost : G.Color →ℝ := shutter G r * (word F A U t i p * juice F s A Y U t R i)

variable {A R r} {n:ℕ}(H : Budget G A n)(hr:r≤dial A)(hY:‖Y‖≤r)(hh:r≤ H.space S.patch S.kernel) (he:arc F (Sum.inl i)⊆R)
section strip
variable {x:G.Color} (hx:x∈ball 0 r)

local notation "U'" => slip F U (Prod.fst i) x
local notation "u" => pluck (G:=G) (Prod.snd i)
include hr hx
lemma word_analytic : ContDiffAt ℝ ω (word F A U t i p) x := by
  have h := (crawl_line F U i hx hr).1
  exact (smooth_read p).contDiffAt.comp (f:=fun z=> t • crawl F A (slip F U i.1 z)) x (h.const_smul t)
lemma word_flow : fderiv ℝ (word F A U t i p) x u=t*run F A t (pderiv i p) U':= by
  let f := fun v:Chip (Needle F G) => read v p; let g:=fun x=> crawl F A (slip F U i.1 x); let w(z):= t • g z; let a:= hunch G i.1
  have he : HasFDerivAt w (t • a) x:= (crawl_line F U i hx hr).2.const_smul t
  change fderiv ℝ (f ∘ w) x u = _
  rw [fderiv_comp x ((smooth_read p).differentiable (by simp) _) he.differentiableAt,he.fderiv,ContinuousLinearMap.comp_apply,_root_.smul_apply]
  rw [show a u=axis i from stride F i, _root_.map_smul]; change t • (Books.derivative f i (w x))=_; rw [show Books.derivative f i (w x)=read (w x) (pderiv i p) from read_derivative p i (w x)]; rfl
variable (hf:vacant F U i.1 r R)
include hf hh hY
local notation "K" => column F A Y R
local notation "a'" => sat F s A t i

private lemma crystal_pass : ContDiffAt ℝ ω a' (K U'):=
  (sew F s t i H (((column_range F Y hr hY (isField F hx hf))).trans hh)).analytic
lemma fruit_diff : ContDiffAt ℝ ω (juice F s A Y U t R i) x:= by
  let f := fun z=> (K) (slip F U i.1 z)
  exact ((crystal_pass F s Y U t i H hr hY hh hx hf).comp (f:=f) x (gut F Y U i hx hr).1).neg.exp
include he in
lemma peel : fderiv ℝ (juice F s A Y U t R i) x u= -(distill F s A t i (K U')) * juice F s A Y U t R i x:= by
  let f:= fun z=> K (slip F U i.1 z); let v:= a' ∘ f; let d:= distill F s A t i (f x)
  have ht : HasFDerivAt v ((fderiv ℝ a' (f x)).comp (reaches F i R)) x:=
    ((crystal_pass F s Y U t i H hr hY hh hx hf).differentiableAt (by simp)).hasFDerivAt.comp x (gut F Y U i hx hr).2
  change fderiv ℝ (fun z=> Real.exp ((-v) z)) x u = -d*_ ; rw [ht.neg.exp.fderiv]; change Real.exp (-v x) * - ((fderiv ℝ a' (f x)) (reaches F i R u)) = -d*Real.exp (-v x)
  rw [strides F i he]; exact mul_comm ..

-- pointwise cancellation of the full restricted integrand
include hB he
lemma adaptation (ht : 0<t) :
    (A.scale*A.J x)* (Cooling.weight F (runway Y) t U' * milled F s A Y t r R i p U')=
         -(packCost F Y t A U i)* (t⁻¹ * fderiv ℝ (caseCost F s A Y U t r R i p) x u) := by
  let w:= word F A U t i p; let j:= juice F s A Y U t R i; let b:= shutter G r
  let d:= distill F s A t i (K U'); let E:= fderiv ℝ b x u; let q:= run F A t (pderiv i p) U'
  let C:= packCost F Y t A U i
  have hw : fderiv ℝ w x u=t*q:= word_flow F U t i p hr hx
  have hp : fderiv ℝ j x u= -d*j x:= peel F s Y U t i H hr hY hh he hx hf
  have hV : fderiv ℝ (caseCost F s A Y U t r R i p) x u= (w x*j x)*E + b x*(w x*(-d*j x)+ j x*(t*q)):= by
    have h1:= ((word_analytic F U t i p hr hx).differentiableAt (by simp)).hasFDerivAt
    have h2:= ((fruit_diff F s Y U t i H hr hY hh hx hf).differentiableAt (by simp)).hasFDerivAt
    change fderiv ℝ (b*(w*j)) _ _= _
    rw [(((smooth_cut G r).differentiable (by simp) x).hasFDerivAt.mul (h1.mul h2)).fderiv]; change b x*(w x* fderiv ℝ j x u + j x*fderiv ℝ w x u) + (w x*j x)*(fderiv ℝ b x u)= _; rw [hw,hp,add_comm]
  have he0 : boxLog A (U' (Prod.fst i))=x:= by unfold slip; rw [Function.update_self]; exact aboard hr hx
  rw [← mul_assoc, conditions F s hB Y H hr hY hh he hf x hx, milled, indicator_of_mem (isField F hx hf),radix,scatter,arrow,he0,hV]
  change (C * j x)*(b x*(w x*(t⁻¹ * d)-q) - t⁻¹ * E * w x)= -C*(t⁻¹*((w x*j x)*E + b x*(w x*(-d*j x) + j x*(t*q))))
  field_simp; ring
end strip

section interval

lemma gram_stay (hg:0<r) : tsupport (caseCost F s A Y U t r R i p)⊆ ball 0 r ∧ HasCompactSupport (caseCost F s A Y U t r R i p) :=
  ⟨Subset.trans tsupport_mul_subset_left (cut_interior hg),(cut_compact (hr:=hg) G).mul_right⟩
include hr hY hh
lemma crown (hf:vacant F U i.1 r R)(hg:0<r) : ContDiff ℝ ∞ (caseCost F s A Y U t r R i p):= by
  apply contDiff_iff_contDiffAt.mpr; intro x
  by_cases hm:x∈tsupport (caseCost F s A Y U t r R i p)
  · have hv : x∈ ball 0 r:= (gram_stay F s Y U t i p hg (R:=R) (A:=A)).1 hm -- notation
    exact (smooth_cut G r).contDiffAt.mul (((word_analytic F U t i p hr hv).of_le le_top).mul ((fruit_diff F s Y U t i H hr hY hh hv hf).of_le le_top))
  apply contDiffAt_const.congr_of_eventuallyEq (f:=fun _ : G.Color=> (0:ℝ)); filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds (show x∈ (tsupport (caseCost F s A Y U t r R i p))ᶜ from hm)] with x hx using image_eq_zero_of_notMem_tsupport hx

lemma stroll (hf:vacant F U i.1 r R)(hg:0<r):
    (∫ x in ball 0 r, fderiv ℝ (caseCost F s A Y U t r R i p) x (pluck (G:=G) i.2))=0:= by
  let g:= caseCost F s A Y U t r R i p; let v:= pluck (G:=G) i.2
  obtain ⟨he,hc⟩:= gram_stay F s Y U t i p hg (R:=R) (A:=A); have hp:= crown F s Y U t i p H hr hY hh hf hg
  have hz : Integrable (fun x=>fderiv ℝ g x v):=((hp.continuous_fderiv (by simp)).clm_apply (g:=fun _=>v) continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have hE := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume) (v:=v) (g:=g) (f:=fun x=> (1:ℝ)) (by simp) (by simpa only [one_mul] using hz) (by simpa only [one_mul] using hp.continuous.integrable_of_hasCompactSupport hc) (fun _ _=> differentiableAt_const _) (fun i _=> hp.differentiable (by simp) i)
  change (∫ x in ball 0 r, fderiv ℝ g x v)=0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (f:=fun x=> fderiv ℝ g x v) (fun x hx=> image_eq_zero_of_notMem_tsupport (f:=fun x=> fderiv ℝ g x v) (by intro hp; exact hx (he (tsupport_fderiv_apply_subset ℝ v hp))))]; simpa using hE

include hB he
lemma from_vacant (hf:vacant F U i.1 r R)(hg:0<r)(ht:0<t):
    (∫ x in sector G r,Cooling.weight F (runway Y) t (Function.update U i.1 x) * milled F s A Y t r R i p (Function.update U i.1 x) ∂G.probHaar) = 0 := by
  have hx := (milled_pass F s Y t r R i p H hr hY hh).meas
  have hy := (Cooling.weight_pass F (runway Y) t hB).toEnvelope.meas
  let v: G.El→ℝ:=fun x=>Cooling.weight F (runway Y) t (update U i.1 x) * milled F s A Y t r R i p (Function.update U i.1 x)
  have hv : Measurable v:=(hy.comp (measurable_update U)).mul (hx.comp (measurable_update U)); change (∫ x in sector G r, v x ∂G.probHaar)=0; rw [fraction H.right hr v hv]
  refine (setIntegral_congr_fun isOpen_ball.measurableSet (g:=fun x=> _ *(t⁻¹*(fderiv ℝ (caseCost F s A Y U t r R i p) x (pluck (G:=G) i.2)))) (fun x hx=> adaptation F s hB Y U t i p H hr hY hh he hx hf ht)).trans ?_
  rw [integral_const_mul,integral_const_mul, stroll F s Y U t i p H hr hY hh hf hg]; simp
lemma exit (ht:0<t)(hg:0<r):
    (∫ x, Cooling.weight F (runway Y) t (Function.update U i.1 x) * milled F s A Y t r R i p (Function.update U i.1 x) ∂G.probHaar)=0:= by
  by_cases hm: vacant F U i.1 r R
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=sector G r)]; exact from_vacant F s hB Y U t i p H hr hY hh he hm hg ht
    intro x hx; rw [milled, indicator_of_notMem (fun h=> hx (by have hm:= h i.1 (has_address F i R he); rwa [Function.update_self] at hm)),mul_zero]
  have he : ∀ x:G.El, milled F s A Y t r R i p (Function.update U i.1 x)=0 :=fun x=> indicator_of_notMem (fun ht=> hm (restores F ht)) _
  simp_rw [he,mul_zero]; simp
end interval
end YM.MatchingLedger.Periodical

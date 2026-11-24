import YM.Frontier6.Bouquet.Meter.Impulse

/-! Legitimacy of fixed-regulator terms even in very small cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I V:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q R:Ensemble} (h:P≤Q)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
    (H: Patron S Q Y) (p:Trip A P) {x:Seats Q}{f:Full (fiber Q)}{B: Balcony Q}
def Active (f:Full (fiber Q))(z:Margin Q P): Prop:= insideCL loft_le z ∈ tsupport (T.film Q P f)
-- continuous everywhere, because geometry checked on a closed set (no shrinking patch interior requirement)
lemma legitimate {z:Margin Q P}(he:Active T f z)(hp:Fair f B x)(i:Q): Appears (B i) z (fun z=>garland h (togetherS K A p (transit h x z)) i):=by
    let u(z:Margin Q P):= transit h x z; let y(v:P):Set E4:= {u z v}; have hu:Continuous u:= (transit_cont h).comp (continuous_const.prodMk continuous_id)
    have hv(j:P):u z j∈ B (assign h j):= Seats_fair h f hp (T.film_support _ _ _ he) _
    apply Appears.product (s:=dialogues h i) (A:=y)
    · intro j hj; exact (members h ..).mp hj ▸ (singleton_subset_iff.mpr (hv j))
    · intro j hj; exact Appears.suit K (((continuous_apply j).comp hu).continuousAt) rfl continuousAt_const -- position rfl annotate
    intro j hj k hk he'; have hh:= Separate.positions h (x:=x) (Separate.excision h T he) he' (((members ..).mp (show j∈dialogues h i from hj)).trans ((members ..).mp (show k∈dialogues h i from hk)).symm); exact Set.disjoint_singleton.mpr hh

lemma further_cont (hh:Gentle H B)(he:Fair f B x): Continuous (ink K A T h x H p f):=by
   let s:= train (fiber Q) (costsD A p) (T.film Q P f); let P' := Margin Q P; let y:Margin Q P→L[ℝ] fiber Q:= insideCL loft_le
   let W(z:Margin Q P) := convey h H (togetherS K A p (transit h x z)); refine continuous_iff_continuousAt.mpr (fun z=>?_); by_cases hz:y z ∈ tsupport s
   · have hw:ContinuousAt W z:=by unfold W; simp_rw [convey_at]; exact hh z _ (legitimate K A T h p (z:=z) (train_support (costsD A p) (T.film Q P f) hz) he) -- elaboration
     exact (s.continuous.comp y.continuous|>.continuousAt).smul hw
   apply ContinuousAt.congr (f:=fun _:Margin Q P=> (0:Y)) (continuousAt_const); filter_upwards [y.continuous.continuousAt.eventually (show (tsupport s)ᶜ∈𝓝 (y z) from (isClosed_tsupport _).isOpen_compl.mem_nhds hz)] with a ha
   change 0=s (y a) • W a; rw [image_eq_zero_of_notMem_tsupport ha,zero_smul]
lemma further_compact (x:Seats Q)(f:Full (fiber Q)): HasCompactSupport (ink K A T h x H p f):=by
   let s:= train (fiber Q) (costsD A p) (T.film Q P f); let y : Full (Margin Q P):= restrictS loft_le 0 s
   have hc : (fun v:Margin Q P=> s (insideCL loft_le v)) = y:=by ext1 a; unfold y; rw [restrict_at,forward,zero_add]
   unfold ink; exact HasCompactSupport.smul_right (f':=fun z:Margin Q P=> convey h H (togetherS K A p (transit h x z))) (f:=fun v:Margin Q P=> s (insideCL loft_le v)) (hc ▸ y.hasCompactSupport) -- syntax & args
lemma further (hh:Gentle H B)(he:Fair f B x): Integrable (ink K A T h x H p f):= Continuous.integrable_of_hasCompactSupport (further_cont K A T h H p hh he) (further_compact K A T h H p x f)
lemma ink_absent {z:Margin Q P}(he: insideCL loft_le z ∉ tsupport f): ink K A T h x H p f z=0:=by unfold ink; rw [image_eq_zero_of_notMem_tsupport (fun ht=> he (T.film_support _ _ _ (train_support _ _ ht))), zero_smul]
lemma gone (F0:R≤Q)(hx: ∀ z∈tsupport f, Separate F0 z)(he:¬ P ≤ R): essay K A T h x H p f=0:=by
   unfold essay; rw [show (fun z=> ink K A T h x H p f z)=fun _=>0 from funext fun z=>?_]; simp
   exact ink_absent K A T h H p (fun hv=> he (Separate.included F0 h (hx _ hv)))
end YM.Frontier6.Bouquet

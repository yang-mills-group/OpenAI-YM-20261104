import YM.MSbar.Scale.Vault
/-! Euler and Laurent polarization commute. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Counter.Crest
open Dim Symbol Domain Diagram Super Scale Scale.Inertia Function Set Filter Complex
open scoped Classical Topology ContDiff BigOperators
variable {C:Type}{W:Edition C}{d: Bit}{m j k i:ℕ}{U:Set ℂ}{A: Mass C}{M: SizeLaw C}{F G H:Functionals C}{z:ℂ}

def jam (A:Mass C) (F:Functionals C):Functionals C:=fun z=> Scale.tick A (F z)
-- at all words, preservation of *global* Winter
lemma winter_keep (h:Winter W d i F): Winter W d i (jam A F):=by
   induction i generalizing F with
   | zero=> change F=0 at h; change jam A F=0; rw [h]; funext z; exact tick_zero A
   | succ i ih=> obtain ⟨g,f,hg,hf,rfl⟩:=h; exact ⟨_,_,ih hg, tick_live (A:=A) hf,funext fun z=>by rw [jam,winter,tick_scale (Live.add hf (hg.live z)),tick_add hf (hg.live z),winter]; rfl⟩
variable [Profit U]
lemma keeps (h:Price i U W d F): Price i U W d (jam A F):= ray_shift (G:=fun _=> A) (fun _=> differentiableOn_const _) h
lemma extraction (h:Price i U W d F): principal W d U (jam A F) = jam A (principal W d U F):=by
   obtain ⟨hc,hd⟩:=h.pair; let P:= principal W d U F; refine is_principal (Price.recognize (keeps (A:=A) hd) (fun z hz=>?_)) (winter_keep hc)
   have he:=h.alive hz; have hh:=hc.live z; change Scale.tick A _-Scale.tick A _= Scale.tick A ((F-_ ) _); simp only [Pi.sub_apply,sub_eq_add_neg]; rw [tick_add he (Live.neg hh), show - (principal W d U F z)=(-1:ℂ) • _ from (by rw [neg_smul,one_smul]), tick_scale hh]; simp only [neg_smul,one_smul]
omit [Profit U] in
lemma lift_equal (h:Live W d (F z))(v:ℕ) : Scale.tick (Scale.mass M v z) (F z)= Scale.tick (Scale.mass M 0 0) (F z) + Scale.slope v z • F z := by
    funext n t; simp only [Scale.tick,Scale.apply_at,Flight.flight,Scale.mass,slope_zero, add_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [ray_center (live_cell h)]; ring
-- powers of slope tagged ℓ, not confluent (for ℓ>0, fixes homo)
def step (v i:ℕ) : ℂ→ℂ := fun z=> (Scale.slope v z)^i
omit [Profit U] in
lemma step_diff (v i:ℕ): DifferentiableOn ℂ (step v i) U:= (holistic U _).pow _
lemma every (v i:ℕ)(h:Price j U W d F): Price j U W d (times (step v i) F):= h.unit (step_diff _ _) -- i duplicated, fix
lemma after (h:Price i U W d F)(he:i≤j) : Regular U W d (times (step k j) F):=by
   obtain ⟨G,hg,hR⟩:= h.grow he; exact ⟨_,hg.scale ((2*(k:ℂ))^j),fun z hz=>by rw [Pi.smul_apply,← hR hz,bare_swell,swell_inner, times,step,Scale.slope,mul_pow,smul_smul]⟩
-- eigen Laurent family homogeneous consequence: analytic? not necessarily, locality in every component.
omit [Profit U] in -- omit i? 
lemma span (h: Winter W d k F) (hx : jam (Scale.mass M 0 0) F=0) (z:ℂ) (t:ℝ) (x:Words C m): ray (F z) x t= if M (skin x)<0 then 0 else ((t:ℂ)^((M (skin x)).toNat))*(F z m x):= locality (h.live z) (by simpa only [jam,no_add] using! congr_fun hx z) t
end YM.MSbar.Counter.Crest

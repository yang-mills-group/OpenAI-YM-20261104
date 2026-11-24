import YM.RGComparison.Core16.Lumen.Blink
/-!
# The actual conditional normalized calculus

Use real mask derivatives just for Hearth estimation. MM near-law proof is on the full
polynomial with prior weights. No flag coalesced outside. Keep β formula evaluated, denominator
same as in Husky & contains blocked noise normalized kernel correction (Fields V actual).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Planet
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T) (g:ℝ)

def bureau:= (P.F g).output g
def pot:= ∫ x,(P.bureau g) x ∂skillet G ι
def expect (f:Sky G ι→ℝ):= (∫ x, P.bureau g x*f x ∂skillet G ι) / P.pot g

variable {P g}(H:P.Steady)(hg:amen X g)
include H hg
lemma bureau_env : Envelope (P.bureau g):= Base.output_env <| H.tickets g hg
lemma bureau_pos (x:Sky G ι): 0<P.bureau g x:= Base.output_pos (H.tickets g hg) _
lemma pot_pos:0<P.pot g := by
    apply (integral_pos_iff_support_of_nonneg (fun x=> (bureau_pos H hg x).le) ((bureau_env H hg).integrable _)).2
    rw [show Function.support _=Set.univ from Set.eq_univ_of_forall (fun i=> (bureau_pos H hg i).ne')]; simp
lemma burden (z:ℝ) : P.expect g (fun _=>z)=z:=by
    unfold expect; rw [integral_mul_const]; change P.pot g*z/P.pot g=z; rw [mul_comm _ z]; exact mul_div_cancel_right₀ z (pot_pos H hg).ne'
lemma regularize {f:Sky G ι→ℝ} (hf: Envelope f) : Integrable (fun x=> P.bureau g x*f x) (skillet G ι):= ((bureau_env H hg).mul hf).integrable _
lemma expect_add {f f':Sky G ι→ℝ}(hf:Envelope f)(hh:Envelope f'):P.expect g (f+f')=P.expect g f+P.expect g f':=by unfold expect; simp only [Pi.add_apply,mul_add,integral_add (regularize H hg hf) (regularize H hg hh),add_div]
lemma expect_sub {f f':Sky G ι→ℝ}(hf:Envelope f)(hh:Envelope f'):P.expect g (f-f')=P.expect g f-P.expect g f':=by unfold expect; simp only [Pi.sub_apply,mul_sub,integral_sub (regularize H hg hf) (regularize H hg hh),sub_div]
variable (g P)
omit H hg [Fintype D] in
lemma expect_mul (r:ℝ)(f: Sky G ι→ℝ): P.expect g (r • f)=r*P.expect g f := by unfold expect; simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm _ r, integral_const_mul,mul_div_assoc]
variable {P g}
lemma paid {K:Type*} (I:Finset K)(f : K→ Sky G ι→ℝ)(hf:∀i∈I,Envelope (f i)): P.expect g (∑ i∈I,f i)=∑ i∈I,P.expect g (f i):=by unfold expect; simp only [Finset.sum_apply,Finset.mul_sum]; rw [integral_finsetSum]; rw [Finset.sum_div]; exact fun i hi=> regularize H hg (hf i hi)
lemma tariff {f f':Sky G ι→ℝ}(hf:Envelope f)(hh:Envelope f')(he: f≤ f'): P.expect g f≤ P.expect g f':=div_le_div_of_nonneg_right (integral_mono (regularize H hg hf) (regularize H hg hh) fun i=> mul_le_mul_of_nonneg_left (he i) (bureau_pos H hg i|>.le)) (pot_pos H hg|>.le)
-- Absolute error budget with support-origins. χ-law inj retained. No need smooth f.
omit H hg in
lemma envelope_hide {K : Type*}[MeasurableSpace K] (s:Set K)(hs:MeasurableSet s)(w: K→ℝ)(hw:Envelope w): Envelope (s.indicator w):= ⟨hw.meas.indicator hs,hw.cost.choose,fun i=> (norm_indicator_le_norm_self w i).trans (hw.cost.choose_spec i)⟩
lemma patch_cost {f:Sky G ι→ℝ}(_hf:Envelope f)(V:Set (Sky G ι))(hV:MeasurableSet V){Q Q' budget:ℝ}(hQ:0≤Q)(hP:0≤ Q') (h:∀x∈V, |f x| ≤ Q) (hd:∀ x∉V, |f x| ≤ Q') (hp:(∫ x in Vᶜ,P.bureau g x ∂skillet G ι)≤ budget* P.pot g):
   |P.expect g f| ≤ Q+ budget*Q':=by
    unfold expect; rw [abs_div,abs_of_pos (pot_pos H hg),div_le_iff₀ (pot_pos H hg)]
    let S' := Vᶜ
    let U := P.bureau g; let M := skillet G ι; let y:= S'.indicator U
    let v (x:Sky G ι):= U x*Q+y x*Q'
    apply (norm_integral_le_of_norm_le (g:=v) (f:=fun x=> P.bureau g x*f x) (μ:=M) (show Integrable v M from (show Envelope v from (((bureau_env H hg).mul (.const Q)).add ((envelope_hide S' hV.compl _ (bureau_env H hg)).mul (.const Q')))).integrable M) ?_).trans
    · change (∫ x,U x*Q+y x*Q'∂M) ≤ (Q+budget*Q')*P.pot g
      rw [integral_add ((bureau_env H hg).integrable M|>.mul_const Q) ((envelope_hide S' hV.compl _ (bureau_env H hg)).integrable M|>.mul_const Q'),integral_mul_const,integral_mul_const,integral_indicator hV.compl]
      change P.pot g*Q+(∫ x in S', U x ∂M)* Q' ≤ _; apply (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hp hP)).trans_eq; ring
    filter_upwards with x; change |U x * f x| ≤ v x; have hu:0≤U x:= (bureau_pos H hg x).le; rw [abs_mul,abs_of_nonneg hu]
    by_cases he:x∈V
    · unfold v; rw [show y x=0 from Set.indicator_of_notMem (Set.notMem_compl_iff.mpr he) _ ,zero_mul,add_zero]; exact mul_le_mul_of_nonneg_left (h _ he) hu
    unfold v; rw [show y x=_ from Set.indicator_of_mem (show x∈S' from he) _]; exact (mul_le_mul_of_nonneg_left (hd _ he) hu).trans (le_add_of_nonneg_left (mul_nonneg hu hQ))
section air
variable (i:Wire G ι){b :ContDiffBump (0:ℝ)}(hQ:Dust b X.δ)
include hQ
def scope (P:Planet X S ι k T) (g:ℝ) (i:Wire G ι)(b:ContDiffBump (0:ℝ))(f f':Sky G ι→ℝ)(x:Sky G ι):= (P.dark b i x)*(P.attr i g x)*f x/g - P.dark b i x*f' x-g*P.faint b i x*f x
lemma breathed {f f':Sky G ι→ℝ}(hG:0<g)(h: ∀ x, HasDerivAt (fun t=> f (raybay i t x)) (f' x/g) 0)(hf:Envelope f)(hh:Envelope f'): P.expect g (P.scope g i b f f')=0:=by
   let B:=P.bureau g; let c := P.scope g i b f f'; let f₁ (x: Sky G ι):= -g*(P.dark b i x*B x * f x); let f₂ (x: Sky G ι):= B x*c x
   have he x: HasDerivAt (fun t=> f₁ (raybay i t x)) (f₂ x) 0:= by
     let u:=raybay i; have hz:u 0 x=x:=gust_zero ..; unfold f₁ f₂; change HasDerivAt (fun t:ℝ=> -g * (P.dark b i (u t x) * B (u t x) * f (u t x))) _ 0
     by_cases hs:crisp X.δ (P.heat i.1) x
     · have h := (((splat (b:=b) (P:=P) i x).fun_mul (reading i H g hg x hs)).fun_mul (h x)|>.const_mul (-g)); apply h.congr_deriv; rw [show raybay i 0 x=_ from hz]; unfold c scope B bureau; field_simp; ring
     have he := away i hQ hs; have h0:P.dark b i x=0:= hz ▸ (show P.dark b i (u 0 x)=0 from he.self_of_nhds)
     have hp:P.faint b i x=0:=(splat i x).unique ((hasDerivAt_const ..).congr_of_eventuallyEq he)
     simp only [c,scope,h0,hp,zero_mul,zero_div,sub_zero,mul_zero]; apply HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0:ℝ) (0:ℝ)); filter_upwards [he] with t ht; change P.dark b i (u t x)=0 at ht; simp [ht]
   have ec : Envelope c := by
      let p:= P.whirl b i; let e:= havenreal (stout i H g)
      unfold c scope; simp_rw [div_eq_mul_inv,sub_eq_add_neg]; exact ((((p.1.mul e).mul hf).mul (Envelope.const _)).add (p.1.mul hh).neg).add ((((Envelope.const g).mul p.2).mul hf).neg)
   have hv:= air i.2 i.1 (f:=f₁) (f':=f₂) ((Envelope.const _).mul (((P.whirl b i).1.mul (bureau_env H hg)|>.mul hf))) ((bureau_env H hg).mul ec) he
   change (∫ x,f₂ x∂skillet G ι)/ _ =0; rw [hv,zero_div]
end air
end YM.RGComparison.Core16.Lumen.Planet

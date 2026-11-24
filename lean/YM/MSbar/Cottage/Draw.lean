import YM.MSbar.Cottage.Model
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{V :Config G c}{R: Rep G f}{σ C T a v δ Δ w b u κ A₀:ℝ}
open Finset RG.PathData Tree Bulk
variable {Y:Support f}
open AnalyticBridge.VerifiedReset Next.Scheduling Precision
variable {F: Forest S.ratio}{X:Finset F.Free}
set_option quotPrecheck false
local notation "I"=> IV F X G
local notation "o!"=> fence F X G
local notation "U!"=> Config G f
local notation "N"=> prior G f
local notation "θ"=> twirl F X
local notation "P"=> boundPress S R V
local notation "Z"=> S.push R.beta R.eval V
local notation "Φ!"=> expect S R V
variable (h: Admitted V R S σ C δ T w)
variable {A:Set (Config G f)}{r:Config G f→ℝ}
namespace Rota
variable (g:Rota (S:=S) R V Y F X A r a κ)(t:IV F X G) (f':Config G f→ℝ) (e:GaugeLocal S Y f') (u:ℝ)(hu : 0 ≤ f')(hb:∀ i, f' i ≤ u)
include h g e
lemma stereo : Envelope (fun p:I×U!=> ghat r p.1 f' A p.2) := ((backdrop (specReady A g.reforms|>.currency) measurable_snd).mul ((backdrop (gaugeMoney g.zoning e|>.currency) ((twirlD F X G).measurable))))
lemma modern : Envelope (fun p:I×U!=>P p.2*ghat r p.1 f' A p.2) := (backdrop (bound_ink h) measurable_snd|>.mul (stereo h g f' e))
lemma tremolo : Envelope (fun p:I×U!=>swapG R (boundPress S R V) p.1 r f' A p.2) :=
   let he:= (twirlD F X G).measurable; let hu:= ((specReady _ g.reforms).currency); (((backdrop (bound_ink h) he).mul (backdrop hu he)).mul ((backdrop g.zoning.currency measurable_snd).mul (backdrop e.currency he)))
local notation "t'"=> (fun i j x=> swapG R (boundPress S R V) i r j A x)
omit h g e in
def resample (F:Forest S.ratio)(X:Finset F.Free)(r : Config G f→ℝ)(A:Set (Config G f)) (f':Config G f→ℝ) (U:Config G f) := ∫ t, ghat (F:=F) r t f' A U∂ fence F X G
local notation "s'"=> resample F X r A
lemma lands : Φ! (s' f')=∫ t:IV F X G,Φ! (ghat r t f' A)∂fence F X G:= by
    simp_rw [readsX h]; rw [integral_div]; apply congr_arg (fun x=> x/Z); unfold resample; simp_rw [← integral_const_mul]; apply Eq.symm; exact integral_integral_swap ((modern h g f' e).integrable ((fence F X G).prod (prior G f))) -- names order
-- reverse integrand directly.S.Specific conditional distribution of t given big logs independent forest outside.
variable (hd:S.patch.Branches S.kernel G)
include hd
lemma respin : (∫ t, (∫ U, t' t f' U∂N)∂o!)=(∫ U,P U*((spec A*f') U)∂ N):=by
    let F'(p:I× U!):=P p.2* spec A p.2*f' p.2*r (θ p.1 p.2)
    have hp: Envelope F':= ((((backdrop (bound_ink h) measurable_snd).mul (backdrop (specReady _ g.reforms|>.currency) measurable_snd)).mul (backdrop e.currency measurable_snd)).mul (backdrop g.zoning.currency ((twirlD F X G).measurable)))
    have he := voyage F X F' hp (fun t i he U=> congr_arg₂ (·*·) (congr_arg₂ (·*·) (congr_arg₂ (·*·) (tonic hd h i he U) ((specReady _ g.reforms).turn i he U)) (e.turn i he U)) ((twisted F X _ g.zoning t (g.orbit t)).turn i he U))
    have ht (U)(t:I): swapG R P t r f' A U= F' (t⁻¹,θ t U):=by unfold swapG F'; dsimp only; rw [pulse U]; ring
    simp_rw [ht]; rw [he, integral_integral_swap (α:=IV F X G) ?_]; swap; · exact hp.integrable _
    unfold F'; dsimp only; simp_rw [integral_const_mul]; apply integral_congr_ae; filter_upwards with U; by_cases h:U∈A; rw [g.fund U h, Pi.mul_apply]; ring
    rw [Pi.mul_apply,show spec A U=0 from Set.indicator_of_notMem h _]; ring
local notation "δ0"=> Δ*(R.p.mass Y (a*u*2)*Real.exp (Y.card*w))
variable (L:MergeProof.Menu.Arsenal R)(H:Psalm S R v Δ)(hc:Continuous R.eval)(hD: ∀ i,0<R.eval i)(ht: flags v V=∅)(hr:0≤ Δ)(hκ:1≤ κ) (hΩ: chance S R V Aᶜ ≤ A₀)
include L H hc hD ht hr hκ hΩ hu hb
def margin (u κ y δ:ℝ) := u*y+ (κ-1)*u+κ*δ
lemma revenue : |Φ! (s' f')-Φ! f'| ≤ margin u κ A₀ (Δ*(R.p.mass Y (a*u*2)*Real.exp (Y.card*w))) :=by
    let p(t:I):= Φ! (ghat r t f' A); let q(t:I):= (∫ U,t' t f' U∂ N)/Z; let r₀:=δ0
    have hκ':0 ≤ κ:=zero_le_one.trans hκ; have he:= lands h g f' e
    have hf : Φ! (spec A*f')=(∫ t,q t∂o!) :=by rw [readsX h, ← respin h g f' e hd, integral_div]; -- q transparency?
    have hG: Integrable q o! := by have he:= unroll (μ:=prior G f) (tremolo h g f' e)|>.integrable o!; exact he.div_const Z
    have hP: Integrable p o! := by unfold p; simp_rw [readsX h]; exact ((unroll (μ:=N) (modern h g f' e)).integrable o!).div_const Z
    let Y₀:=Φ! (spec A*f'); let f₀:=Φ! (s' f'); have hx(t:I):=event h g t f' e u hu hb L H hd hc hD ht hr (zero_le_one.trans hκ)
    have hh : f₀ ≤ κ*Y₀+r₀:=by
       have hz:=integral_mono hP ((hG.const_mul κ).add (integrable_const (μ:=o!) r₀)) (show p ≤ fun i:I=> κ*q i+r₀ from fun t=> hx t|>.1)
       unfold f₀ Y₀; rw [he,hf]; simpa only [Pi.add_apply,integral_add (hG.const_mul κ) (integrable_const (μ:=o!) r₀),integral_const_mul,integral_const,probReal_univ,one_smul] using hz
    have hw : Y₀ ≤ κ* (f₀+r₀):= by
       have hz:=integral_mono hG ((hP.add (integrable_const (μ:=o!) r₀)).const_mul κ) (show q ≤ fun i:I=> κ*(p i+r₀) from fun t=> hx t|>.2)
       unfold f₀ Y₀; rw [he,hf]; simpa only [Pi.add_apply,integral_add hP (integrable_const (μ:=o!) r₀),integral_const_mul,integral_const,probReal_univ,one_smul] using hz
    let W:=Φ! f'; have hb0:0 ≤ u:=le_trans (hu 1) (hb 1); have hW : W-Y₀ ≤ A₀*u∧ Y₀ ≤ W∧ W ≤ u :=by
        let L:= spec A; let v:= spec (Aᶜ); have hL:=specReady _ g.reforms; have hv:= specReady (Aᶜ) (g.reforms.neg)
        have hc (i): L i+ v i=1:=by unfold L v spec; by_cases hh:i∈A; simp [Set.indicator,hh]; simp [Set.indicator,hh]
        have hI(i):0≤ L i ∧ 0≤ v i:=⟨Set.indicator_nonneg (fun _ _=>zero_le_one) _,Set.indicator_nonneg (fun _ _=>zero_le_one) _⟩
        have hs : Y₀+Φ! (v*f')=W:=by
           change Φ! (L*f')+ _ = _; rw [← e_sum V h (show Envelope (L*f') from hL.currency.mul e.currency) (show Envelope (v*f') from hv.currency.mul e.currency)]; exact congr_arg _ (show L*f'+v*f'=f' from funext fun i=>by simp only [Pi.add_apply,Pi.mul_apply]; rw [← add_mul,hc i,one_mul])
        have hu₀:= Bulk.nn V h (hv.currency.mul e.currency) (Envelope.const 0) (fun i=> mul_nonneg (hI i|>.2) (hu i)); have hy (i):v i* f' i ≤ u*v i:= (mul_le_mul_of_nonneg_left (hb i) (hI i|>.2)).trans_eq (mul_comm _ _); have hz₀:= Bulk.nn V h (show Envelope (u • v) from (Envelope.const u).mul hv.currency) (hv.currency.mul e.currency) hy; rw [e_mul] at hz₀
        refine ⟨?_,?_,(Bulk.nn V h (Envelope.const u) e.currency hb).trans_eq (e_const V h u)⟩
        · have hp: Φ! (v*f') ≤ A₀*u:= hz₀.trans ((mul_le_mul_of_nonneg_left hΩ hb0).trans_eq (mul_comm _ _)); linarith only [hs,hp]
        have he : 0≤ Φ! (v*f') := by exact (show Φ! (fun _=>0)=0 from e_const V h 0).symm.trans_le hu₀
        linarith only [he,hs]
    have hB:=hW.2.1.trans hW.2.2
    have h₁ :0≤ A₀ := (chance_pos h g.reforms.neg.from_here).trans hΩ; have hV:0 ≤ r₀:= by have hr':0≤a:=g.rate_pos; unfold r₀ BudgetPoint.mass; positivity
    change |f₀-W|≤ margin u κ A₀ r₀; unfold margin; apply abs_le.mpr; constructor
    · -- from hw Y₀/κ.Easy suppose f₀>u
      by_cases hk:f₀ ≤ u; linarith only [mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr hκ), hw,hW.1]
      linarith only [not_le.mp hk,hW.2.2,mul_nonneg hb0 h₁,mul_nonneg (sub_nonneg.mpr hκ) hb0,mul_nonneg hκ' hV]
    linarith only [hh,hW.2.1,mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hκ),mul_nonneg (sub_nonneg.mpr hκ) hV,mul_nonneg hb0 h₁]
end Rota
end YM.MSbar.Heath.Cottage

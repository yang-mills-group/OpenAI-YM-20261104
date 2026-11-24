import YM.MSbar.Cottage.Ivy
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{V :Config G c}{R: Rep G f}{σ C T a v δ Δ w b u κ A₀:ℝ}
open Finset RG.PathData Tree Bulk
variable {Y:Support f}
open AnalyticBridge.VerifiedReset Next.Scheduling Precision
variable (F: Forest S.ratio)(X:Finset F.Free)
set_option quotPrecheck false
local notation "I"=> IV F X G
local notation "o!"=> fence F X G
local notation "U!"=> Config G f
local notation "N"=> prior G f
local notation "θ"=> twirl F X
structure GaugeLocal (S:StepData c f)(Y:Support f)(p:Config G f→ℝ):Prop where
   currency: RG.Envelope p
   turn : S.Inner p
   located : LocalOn Y p
lemma gaugeMoney {P P':U!→ℝ} {Y:Support f}(h:GaugeLocal S Y P)(g: GaugeLocal S Y P'):GaugeLocal S Y (P*P'):= ⟨h.currency.mul g.currency,fun p hp _=> congr_arg₂ (·*·) (h.turn p hp _) (g.turn p hp _),fun U V e=> congr_arg₂ (·*·) (h.located U V e) (g.located U V e)⟩
lemma specReady (A:Set U!)(h:Seal S Y A) : GaugeLocal (G:=G) S Y (spec A):=by
   refine ⟨RG.Envelope.piece h.from_here (RG.Envelope.const _) (RG.Envelope.const _),?_,?_⟩
   · intro i he U; by_cases hv:U∈A; unfold spec; rw [Set.indicator_of_mem hv,Set.indicator_of_mem ((h.within i he U).1 hv)]; unfold spec; rw [Set.indicator_of_notMem hv,Set.indicator_of_notMem ((h.within i he U).not.mp hv)]
   intro U V e; by_cases hv:U∈A; unfold spec; rw [Set.indicator_of_mem hv,Set.indicator_of_mem ((Iff.of_eq (h.localized U V e)).mp hv)]; unfold spec; rw [Set.indicator_of_notMem hv,Set.indicator_of_notMem ((Iff.of_eq (h.localized U V e)).not.mp hv)]
lemma twisted {Y:Support f} (p:U!→ℝ)(e:GaugeLocal S Y p) (j:I) (h: Booking Y F (pegged F X j)):GaugeLocal S Y (p ∘θ j):= ⟨backdrop e.currency ((pedaling F (pegged F X j)).measurable), fun i hi U=> (congr_arg p (dodge F (pegged F X j) i U hi)).trans (e.turn i hi _),fun U V hv=> e.located _ _ (listed F (pegged F X j) h _ _ Y subset_rfl hv)⟩
variable (h: Admitted V R S σ C δ T w)
local notation "P"=> boundPress S R V
local notation "Z"=> S.push R.beta R.eval V
local notation "Φ!"=> expect S R V
-- Interior r kernel. Support exactly A∩G. No mixing assumed.
structure Rota (R:Rep G f) (V:Config G c)(Y:Support f)(F:Forest S.ratio)(X:Finset F.Free)(A:Set (Config G f))(r:Config G f→ℝ)(a κ:ℝ):Prop where
    reforms : Seal S Y A
    orbit(t:IV F X G) : Booking Y F (pegged F X t)
    zoning : GaugeLocal S Y r
    paid(t:IV F X G) (U): U∈A → twirl F X t U∈A → flags R.p.threshold (twirl F X t U)=flags R.p.threshold U
    lower : 0 ≤ r
    upper U : r U ≤ a
    ext U : U∉A → r U=0
    price (t:IV F X G) (U): U∈A→twirl F X t U∈A→
             S.density R.beta U V*r (twirl F X t U)*Real.exp (R.exponent U - R.exponent (twirl F X t U)) ≤ κ*(S.density R.beta (twirl F X t U) V*r U)
    fund(U): U∈A→(∫ t:IV F X G,r (twirl F X t U)∂fence F X G)=1
variable {F X} {A:Set (Config G f)}{r:Config G f→ℝ}
namespace Rota
variable (g:Rota (S:=S) R V Y F X A r a κ)(t:IV F X G) (f':Config G f→ℝ) (e:GaugeLocal S Y f') (u:ℝ)(hu : 0 ≤ f')(hb:∀ i, f' i ≤ u)
-- local nonnegative weight
include g
lemma rate_pos : 0≤a:= le_trans (g.lower 1) (g.upper _)
omit g in
def ghat (p:Config G f→ℝ) (t: IV F X G)(f':Config G f→ℝ) (A:Set (Config G f)) (i: Config G f): ℝ:=spec A i * (p (twirl F X t i) * f' (twirl F X t i))
local notation "Yθ"=> ghat r t f' A
include hu hb
lemma positive(U): 0 ≤ ghat r t f' A U :=mul_nonneg (Set.indicator_nonneg (fun _ _=>zero_le_one) _) (mul_nonneg (g.lower _) (hu _))
include e
lemma existent : Tracks R Y (θ t) (ghat r t f' A) S (a*u):=by
    let s:= pegged F X t; let h:= θ t
    have hQ: GaugeLocal S Y Yθ:=gaugeMoney (specReady A g.reforms) (twisted _ _ _ (gaugeMoney g.zoning e) _ (g.orbit t))
    refine ⟨hQ.turn,fun U V e _=> hQ.located _ _ e,hQ.currency.meas,fun i=>?_,(pedaling F _).measurable,fun i hi=> ?_,fun U V Pt _ hp he _=>listed F s (g.orbit t) _ _ Pt hp he,fun i U hi _=>(dodge F s _ _ hi),fun X U hv he x hl hh=> ?_⟩
    · rw [abs_of_nonneg (positive g t f' u hu hb _)]; by_cases hh:i∈ A
      · change spec A i * (r (θ t i)* f' _)≤ _; rw [show spec A i=1 from Set.indicator_of_mem hh _,one_mul]; exact mul_le_mul (g.upper _) (hb _) (hu _) (rate_pos g)
      change spec A i * (r (θ t i)* f' _)≤ _; rw [show spec A i=0 from Set.indicator_of_notMem hh _,zero_mul]; exact mul_nonneg (rate_pos g) (le_trans (hu i) (hb i))
    · change spec A i * (r (θ t i)*f' (θ t i)) ≠ 0 at hi
      apply g.paid
      · exact by_contra fun hb=> hi (by rw [show spec A i=0 from Set.indicator_of_notMem hb _,zero_mul])
      exact by_contra fun hb=> hi (by rw [g.ext _ hb,zero_mul,mul_zero])
    exact (unspoken F s (g.orbit t) U x (fun i=>disjoint_left.mp he i hl)).symm
omit e g hu hb in
lemma pulse (W: Config G f)(t:IV F X G): twirl F X t⁻¹ (twirl F X t W)=W:= by rw [ends, inv_mul_cancel, stay]
variable (L:MergeProof.Menu.Arsenal R)(H:Psalm S R v Δ)(hd:S.patch.Branches S.kernel G)(hc:Continuous R.eval)(hD: ∀ i,0<R.eval i)(ht: flags v V=∅)(hr:0≤ Δ)(hκ:0≤ κ)
include h L H hd hc hD ht hr hκ
-- yH exchange sandwich via receipt.
omit hd in
def swapG (R:Rep G f)(Q:U!→ℝ)(t:IV F X G) (r:Config G f→ℝ)(f':Config G f→ℝ)(A:Set (Config G f))(U:Config G f):=Q (twirl F X t U)* spec A (twirl F X t U)*(r U*f' (twirl F X t U)) -- R unused
local notation "p!"=>swapG R (boundPress S R V) t r f' A
lemma event :
    Φ! (ghat r t f' A) ≤ κ * ((∫ i,p! i∂ N)/Z) + Δ*(R.p.mass Y (a*u*2)* Real.exp (Y.card*w)) ∧
    ((∫ i, p! i ∂N)/Z) ≤ κ*(Φ! (ghat r t f' A)+ Δ*(R.p.mass Y (a*u*2)* Real.exp (Y.card*w))) := by -- second direction factor? pointwise inv.Ratio reverse via price for t⁻¹.So ctx.
    let β'(i:U!):= R.eval (θ t i)/R.eval i*Real.exp (R.exponent i-R.exponent (θ t i))
    have hF:RG.Envelope β':=by
       have hh : Measurable (θ t):= (pedaling F _).measurable; let a:=R.exponent; have hi:RG.Envelope a:= R.exponentEnv h.lawful; have hc: Continuous (fun i=>(R.eval i)⁻¹):=hc.inv₀ (fun i=>(hD i).ne')
       obtain ⟨b,hB⟩:=(isCompact_range hc.norm|>.bddAbove); unfold β'; simp_rw [div_eq_mul_inv,sub_eq_add_neg]
       exact (((backdrop (R.envelope h.lawful) hh).mul ⟨hc.measurable,b,fun i=>hB ⟨i,rfl⟩⟩).mul ((hi.add (backdrop hi hh|>.neg)).exp))
    have hp := existent g t f' e u hu hb; let p:= Yθ
    have hP : RG.Envelope p:=by
       let J:=g.reforms; exact (show GaugeLocal (G:=G) S Y p from gaugeMoney (specReady _ g.reforms) (twisted F X _ (gaugeMoney g.zoning e) t (g.orbit t))).currency
    let δ₀:= Δ*(R.p.mass Y (a*u*2)*Real.exp (Y.card*w)); let q:= Φ! (p*β'); have hu': |q-Φ! p| ≤ δ₀:= by
       have hz := Bulk.receipt V h hp L H hr ht hD; change |Φ! (fun i=> p i *(β' i-1))|≤δ₀ at hz
       suffices h : Φ! (fun i=> p i*(β' i-1))= q-Φ! p by rwa [h] at hz
       let s (i):= p i*(β' i-1); have he:RG.Envelope s:=hP.mul (by simp_rw [sub_eq_add_neg]; exact hF.add (RG.Envelope.const _))
       apply eq_sub_of_add_eq; rw [← e_sum V h he hP]; exact congr_arg _ (show s+p=p*β' from funext fun i=> by simp only [Pi.add_apply,Pi.mul_apply]; unfold s; ring)
    let w'(i):=p! i; have hg: RG.Envelope w':=by
       have hk:Measurable (θ t):=(pedaling F _).measurable
       exact ((backdrop (bound_ink h) hk).mul (backdrop (specReady _ g.reforms|>.currency) hk)).mul (g.zoning.currency.mul (backdrop e.currency hk))
    let x'(i):= boundPress S R V i*(p*β') i; have hx:RG.Envelope x':=(bound_ink h).mul (hP.mul hF)
    have hc(i:U!): x' i ≤ κ*w' i∧ w' i ≤ κ*x' i:=by
       let U:= θ t i; by_cases hi:i∈A
       · by_cases hh:U∈A
         · let j:= R.exponent i-R.exponent U; have hk:x' i=(S.density R.beta i V*r U*Real.exp j)*(R.eval U * f' U):=by
              unfold x'; rw [Pi.mul_apply,show p i=r U*f' U from (by unfold p ghat; rw [show spec A i=1 from Set.indicator_of_mem hi _,one_mul])]; unfold β' j boundPress; unfold U; field_simp [(hD _).ne']
           have hA': w' i=(S.density R.beta U V*r i)*(R.eval U*f' U):=by unfold w' swapG; rw [show spec A (θ t i)=1 from Set.indicator_of_mem hh _,mul_one]; unfold boundPress U; ring
           rw [hk,hA']; constructor
           · rw [←mul_assoc κ]; exact mul_le_mul_of_nonneg_right (g.price t i hi hh) (mul_nonneg (hD _).le (hu _))
           rw [←mul_assoc κ]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hD _).le (hu _)); have hp := g.price t⁻¹ U hh (show θ t⁻¹ U∈A from (pulse i t|>.symm ▸ hi)); rw [show θ t⁻¹ U=i from pulse i t,← neg_sub,Real.exp_neg,← div_eq_mul_inv] at hp; exact ((div_le_iff₀ (Real.exp_pos _)).1 hp).trans_eq (mul_assoc ..)
         rw [show w' i=0 from (by unfold w' swapG; rw [show spec A (θ t i)=0 from Set.indicator_of_notMem hh _,mul_zero,zero_mul]),show x' i=0 from ?_]; · simp
         unfold x'; rw [Pi.mul_apply,show p i=0 from (by unfold p ghat; rw [g.ext (θ t i) hh,zero_mul,mul_zero])]; ring
       have hpi:p i=0:=by unfold p ghat; rw [show spec A i=0 from Set.indicator_of_notMem hi _,zero_mul]
       rw [show w' i=0 from (by unfold w' swapG; rw [g.ext i hi,zero_mul,mul_zero]), show x' i=0 from (by unfold x'; rw [Pi.mul_apply,hpi,zero_mul,mul_zero])]; simp
    let Ω:= (∫ i,w' i∂N)/Z; have hZ : q=(∫ i,x' i∂N)/Z:=readsX h _
    have hz₀ : q ≤ κ*Ω:= by rw [hZ,show κ*Ω=_ from (mul_div_assoc κ (∫ i,w' i∂N) Z).symm]; apply div_le_div_of_nonneg_right _ h.mass.le; rw [←integral_const_mul]; exact integral_mono (hx.integrable _) ((hg.integrable _).const_mul κ) (fun i=>hc i|>.1)
    have hz : Ω ≤ κ*q:=by rw [hZ,← mul_div_assoc]; apply div_le_div_of_nonneg_right _ h.mass.le; rw [←integral_const_mul]; exact integral_mono (hg.integrable _) ((hx.integrable _).const_mul κ) (fun i=>hc i|>.2)
    exact ⟨by change Φ! p ≤ κ*Ω +δ₀; linarith only [hz₀,(abs_le.mp hu').1],hz.trans (mul_le_mul_of_nonneg_left (by linarith only [(abs_le.mp hu').2]) hκ)⟩
end Rota
end YM.MSbar.Heath.Cottage

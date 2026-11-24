import YM.MSbar.Pulse.Wait
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Portal
open Function Filter MeasureTheory Cacao PowerSeries Finset
open scoped Topology Classical BigOperators
local notation "G"=>PowerSeries ℝ
local notation "µ"=>PowerSeries.coeff
variable {α : Type*} [MeasurableSpace α] (ρ:Measure α) [IsProbabilityMeasure ρ]
variable {a b c t x v e d₀ h r A w B s U D δ : ℝ} {p m : ℕ}{f g : α→ℝ}{Y:Set α}
-- Inactive cost, all envelopes. Operational: log defined on purchased read domain, Bochner integrable tails, A estimate uniform.
def mug (a:α→ℝ)(x:ℝ):= (∫ y:α,a y∂ρ) + x -- unused
def purse (Y:Set α)(g:α→ℝ) := Y.indicator (fun x=> Real.exp (g x))
lemma ban (f : α→ℝ)(hf:Integrable f ρ) (hy: MeasurableSet Y) (g :α→ℝ) (hg: Integrable g ρ)(hu:∀ i,i∉Y→f i=0)(he:∀ i,i∈Y →|f i-g i| ≤ a)(hp:0≤ a) (hx: |∫ i in Yᶜ,g i∂ρ| ≤ t):
   |(∫ i,f i∂ρ) - ∫ i,g i∂ρ| ≤ a+t:=by
   rw [← integral_add_compl hy hg, ← integral_add_compl hy hf, show (∫ i in Yᶜ,f i∂ρ)=0 from ?_,add_zero,← sub_sub,← integral_sub hf.integrableOn hg.integrableOn]; swap; · apply setIntegral_eq_zero_of_forall_eq_zero; exact fun i hi=>hu i hi
   apply (abs_sub _ _).trans (add_le_add _ hx); refine (norm_integral_le_integral_norm (fun i=>f i-g i)).trans ?_
   apply (setIntegral_mono_on ((hf.sub hg).integrableOn.norm) (integrableOn_const (by simp)) hy he).trans; rw [setIntegral_const,smul_eq_mul]; exact mul_le_of_le_one_left hp (le_trans (measureReal_mono (Set.subset_univ _) (by simp)) probReal_univ.le)
structure Survey (Y:Set α)(Q H:α→PowerSeries ℝ)(f g d:α→ℝ) (p:ℕ) (t r a B c D b K X:ℝ): Prop where
   zone : MeasurableSet Y
   fullC: Integrable (purse Y g) ρ
   markC: Integrable ((purse Y g)*f) ρ
   heatQ (v:ℕ) :Integrable (fun i=>µ v (Spring (Q i))) ρ
   heatM (v:ℕ) :Integrable (fun i=>µ v ((H i)* Spring (Q i))) ρ
   vacuumT (i:α) : Kind (Q i)
   aura : 0 ≤ t
   young : t ≤ 1
   funnel : t*K ≤ b
   paid (i:α) : i∈Y → Belt p (Q i) ≤ K ∧ Belt p (H i) ≤ c
   rareT: Measurable f -- can use solely restricted
   ember : Integrable d ρ
   emberM: Integrable (fun i=> d i*µ 0 (H i)) ρ
   bits i :i∈Y → |d i|≤ B ∧ |g i-taste p (Q i) t-d i|≤ D ∧ |f i-taste p (H i) t| ≤ X
   tails : |∫ i in Yᶜ,taste p (Spring (Q i)) t +d i∂ρ| ≤a
   tailsM: |∫ i in Yᶜ,taste p (H i* Spring (Q i)) t+d i *µ 0 (H i)∂ρ| ≤r
-- simple. Add scalar moment tail.Belt.Bern cost.
variable (Q H:α→PowerSeries ℝ)(f g d':α→ℝ) (T: Survey ρ Y Q H f g d' p t r a B c D b h s)
local notation "q₀"=>purse Y g
namespace Survey
variable {ρ Q H f g d'}
local notation "ψ!"=> (fun h:α→ℝ=> ∫ t,h t∂ρ)
local notation "C₀"=> deltaC D B h 0 0 b t p
local notation "A₀"=> debit p h b B D t s C₀ c
include T
lemma stars (he: Y.Nonempty) :
    |(∫ i:α,q₀ i∂ρ)-(∫ i,taste p (Spring (Q i)) t ∂ρ)-∫ i,d' i∂ρ|≤ C₀+a∧
    |(∫ i:α,q₀ i*f i∂ρ)-(∫ i,taste p (H i*Spring (Q i)) t ∂ρ)-∫ i,d' i*µ 0 (H i)∂ρ| ≤ A₀+r:=by
    let d:= C₀; let z:= A₀; obtain ⟨i,he⟩:= he; have Hp(j u) := stat p t h (g j) (d' j) D b (S:=0) (D:=0) (r:=B) (T.vacuumT j) ((T.paid j u).1) T.funnel T.aura T.young (T.bits j u|>.1) (T.bits j u|>.2.1)
    have Hm(j)(hx:j∈Y): |Real.exp (g j)* f j - taste p (H j*Spring (Q j)) t -d' j*µ 0 (H j)|≤ z := scan p _ _ (d' j) D _ c _ s d (T.vacuumT j) T.aura T.young (T.paid j hx|>.2) (T.paid j hx|>.1) (Hp j hx|>.1) (Hp j hx|>.2) (T.bits j hx|>.1) (T.bits j hx|>.2.2) -- order
    have ht(F :α→PowerSeries ℝ)(h: ∀ i,Integrable (fun v=>µ i (F v)) ρ):Integrable (fun i:α=>taste p (F i) t) ρ:=by unfold taste; exact MeasureTheory.integrable_finset_sum _ (fun i _=>(h i).const_mul _)
    let X i:=taste p (Spring (Q i)) t; let W i:=taste p (H i*Spring (Q i)) t; let U i:=d' i *µ 0 (H i)
    have hx:= ht _ T.heatQ; have hu:= ht _ T.heatM; constructor
    · rw [sub_sub,← integral_add hx T.ember]; refine ban ρ _ T.fullC T.zone _ (hx.add T.ember) (fun i hi=>Set.indicator_of_notMem hi _) (fun i h=>?_) ((abs_nonneg _).trans ((Hp i he).1)) T.tails
      rw [show q₀ i= Real.exp (g i) from Set.indicator_of_mem h _,← sub_sub]; exact Hp i h|>.1
    rw [sub_sub,← integral_add hu T.emberM]; refine ban ρ _ T.markC T.zone _ (hu.add T.emberM) (fun i hi=>?_) (fun i hi=> ?_) ((abs_nonneg _).trans (Hm i he)) T.tailsM
    · rw [Pi.mul_apply,show q₀ i=0 from Set.indicator_of_notMem hi _,zero_mul]
    rw [Pi.mul_apply,show q₀ i= Real.exp (g i) from Set.indicator_of_mem hi _,← sub_sub]; exact Hm i hi
variable (I O :PowerSeries ℝ)
-- compare to scalar polys. Requirements.Intent.At zeropoint.I.Compens.:pk.Normal.C.Un.Vc
local notation "I₀"=> taste p I t
local notation "O₀"=> taste p O t
-- Let elementary ΔΠ formula explicit.B.Price denomin, linear covariance d'
omit T in
def fee (p:ℕ) (c i r x z z' w h w':ℝ) := c^(p+1)*(i*r) + z'+ i*z+ x*(c*i) + h*w' -- unused
lemma magnitude (he:Y.Nonempty) (hc : µ 0 I=1) (hz : (∫ i,taste p (Spring (Q i)) t∂ρ)=I₀) (hu : (∫ i,taste p (H i*Spring (Q i)) t∂ρ)=taste p (O*I) t) (hp : |∫ i,d' i∂ρ| ≤ x)(hq: |(∫ i,d' i * (µ 0 (H i))∂ρ) - (∫ i,d' i∂ρ)*µ 0 O|≤ v)
   (hF:Belt p I≤ A)(hχ:Belt p O≤ w) (hK : t*A+x+(C₀+a) ≤ 1/2) :
   let V:=∫ i, q₀ i ∂ρ
   let z:=∫ i,d' i ∂ρ
   let V' := (∫ i,d' i * µ 0 (H i) ∂ρ) - z*µ 0 O
   1/2 ≤ V ∧ |(∫ i,q₀ i*f i∂ρ)/V-(O₀+V')|≤ 2 * fee p t w A x (C₀+a) (A₀+r) w v (t*A+x+(C₀+a)):=by -- fee args need check x*(c*O),X. r*w typo.
    intro V z V'
    let y:= I₀; let Z:=O₀; let m:=∫ i,q₀ i*f i∂ρ; let d:=C₀+a; let s':= t*A+x+d; let D':=A₀+r; have hb:=T.aura; have hi:=T.young; let k:=taste p (O*I) t
    obtain ⟨h₀,hP⟩:= stars T he; rw [hz] at h₀; rw [hu] at hP
    have hI:|I₀-1|≤ t*A:= by have h:=sauce I p hb hi; rw [hc] at h; exact h.trans (mul_le_mul_of_nonneg_left hF hb)
    have hL:|V-1|≤ s' := by rw [show V-1=(V-y-z)+(y-1)+z by abel]; refine (abs_add_le ..).trans ((add_le_add ((abs_add_le ..).trans (add_le_add h₀ hI)) hp).trans_eq ?_); unfold s' d; ring
    have hV:1/2 ≤ V:= by -- linarith
       have he:= (abs_le.mp hL).1; linarith only [he,(show s'≤ 1/2 from hK)]
    have hG:|k- Z* y|≤t^(p+1)*(w*A) := (taste_mul p _ hb hi O I).trans (mul_le_mul_of_nonneg_left (mul_le_mul hχ hF (Belt_pos ..) ((Belt_pos ..).trans hχ)) (pow_nonneg hb _))
    have hG':|Z| ≤ w:=(taste_pays hb hi O).trans hχ
    refine ⟨hV,?_⟩; let X:=fee p t w A x d D' w v s'; have ht:0 < V:=lt_of_lt_of_le (by norm_num) hV; rw [show ((∫ i,q₀ i*f i∂ρ)/V)-(O₀+V')=(m-(Z+V')*V)/V from (by unfold m Z; field_simp),abs_div,abs_of_pos ht,div_le_iff₀ ht];
    have hM:|m-(Z+V')*V| ≤ X:= by
        let X':= V-y-z; let W:= (∫ i,d' i*µ 0 (H i)∂ρ); have hb: m-(Z+V')*V = (k-Z*y)+(m-k-W) - X'*Z-z*(Z-µ 0 O)-V'*(V-1):=by unfold X' W V'; ring
        have h₁:= abs_sub (k-Z*y+(m-k-W)-(X'*Z) - z*(Z-µ 0 O)) (V'*(V-1))
        rw [hb]; apply h₁.trans; refine add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_
        · apply (abs_sub _ _).trans; refine add_le_add ((abs_add_le ..).trans (add_le_add hG hP)) ?_; rw [abs_mul,mul_comm]; exact mul_le_mul hG' h₀ (abs_nonneg _) ((abs_nonneg _).trans hG')
        · rw [abs_mul]; exact mul_le_mul hp ((sauce O p T.aura T.young).trans (mul_le_mul_of_nonneg_left hχ T.aura)) (abs_nonneg _) ((abs_nonneg _).trans hp)
        rw [abs_mul]; exact mul_le_mul hq hL (abs_nonneg _) ((abs_nonneg _).trans hq)
    apply hM.trans; change X≤ 2*X*V; have hc:0≤X:=(abs_nonneg _).trans hM; linarith only [mul_le_mul_of_nonneg_left hV hc]
end Survey
end YM.MSbar.Bakery.Portal

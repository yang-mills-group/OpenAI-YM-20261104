import YM.OPE.Compatible.Crib.Warm
/-! # law numeric cumul about mark. Horizontal morph order2. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra GaussianScore Stranded Jargon Cinders
variable {I J X:Type*}{s t r:ℝ}{i j:ℕ}
variable [MeasurableSpace X]
section
variable (μ:Measure X)
abbrev a_ (p:X→ℝ):=∫ x,p x ∂μ
abbrev ηAvg (f:X→Token):Token:= ⟨a_ μ fun i=>(f i).s,a_ μ fun i=>(f i).l,a_ μ fun i=>(f i).h⟩
noncomputable def κ2 (f g:X→ℝ):=a_ μ (f*g)-a_ μ f*a_ μ g
noncomputable def κ3 (f g h:X→ℝ) := a_ μ (f*g*h)-a_ μ (f*g)*a_ μ h-a_ μ (f*h)*a_ μ g-a_ μ f*a_ μ (g*h)+ 2*a_ μ f*a_ μ g*a_ μ h
noncomputable def Speak(p:X→Token)(f:X→Token):Token:=ηAvg μ (f*p)/ηAvg μ p
namespace Lav
-- integrability closure
abbrev Pu (p:X→ℝ):Prop:=∀ i:ℕ,0 < i → ∃ t:ℝ,Fault μ i p t
variable {μ} {w y f g a b c:X→ℝ} [IsProbabilityMeasure μ]
lemma Irite (h:Pu μ w): Integrable w μ:= by obtain ⟨a,h⟩:=h 1 zero_lt_one; exact h.rich.integrable (by simp)
lemma flipP (x:ℝ): Pu μ (fun _=>x):= fun _ _=> ⟨_,Fault.constant _⟩
omit [IsProbabilityMeasure μ] in lemma scaleP (h:Pu μ w)(x:ℝ): Pu μ (x • w):= by intro i hi; obtain ⟨a,h⟩:=h i hi; exact ⟨_, h.scaling _⟩ -- unused ν
omit [IsProbabilityMeasure μ] in lemma timesP (h: Pu μ w)(hp:Pu μ y): Pu μ (w*y):=by intro i hi; obtain ⟨a,h⟩:= h (2*i) (by omega); obtain ⟨b,he⟩:=hp (2*i) (by omega); exact ⟨_,h.double he hi⟩
omit [IsProbabilityMeasure μ] in lemma addedP (h:Pu μ w)(hp:Pu μ y):Pu μ (w+y):=by intro i hi; obtain ⟨a,h⟩:=h i hi; obtain ⟨b,hp⟩:=hp i hi; exact ⟨_,h.add hp hi⟩
lemma Etick (h:Pu μ w)(hp:Pu μ y):a_ μ (w+y)=a_ μ w+a_ μ y:=integral_add (Irite h) (Irite hp)
lemma Stats (f g a b c:X→ℝ)(hx:Pu μ f)(hv:Pu μ g)(ha:Pu μ a)(hb:Pu μ b)(hc:Pu μ c):
      Speak μ (fun x=>⟨1,f x,g x+ (2:ℝ)⁻¹*f x^2⟩) (fun x=>⟨a x,b x,c x⟩)= ⟨a_ μ a,a_ μ b+κ2 μ a f, a_ μ c+κ2 μ a g+κ2 μ b f + (2:ℝ)⁻¹*κ3 μ a f f⟩:=by
           let p := (f*f); let u:ℝ:=(2:ℝ)⁻¹; let t:=g+u • p; let P(x):Token:=⟨1,f x,g x+(2:ℝ)⁻¹*f x^2⟩; let q(x):Token:=⟨a x,b x,c x⟩; have hψ: (fun x=>(P x).h)=t:= funext fun x=>by unfold P; dsimp; unfold t p u; simp only [Pi.add_apply, Pi.smul_apply,Pi.mul_apply,sq,smul_eq_mul];
           let X:= ηAvg μ P; let Y:=ηAvg μ (q*P); have hs:X.s=1:=by change a_ μ (fun _=>1)=1; unfold a_;simp
           have hg:a_ μ t = a_ μ g+u*a_ μ p:= by unfold t; rw [Etick hv (scaleP (timesP hx hx) _)]; exact congr_arg (a_ μ g+·) (integral_const_mul ..)
           have hX: X.h=_:= (congr_arg (a_ μ) hψ).trans hg
           have hY: Y.s=a_ μ a:= congr_arg _ (funext (show ∀ i,((q*P) i).s=a i from (fun x=>mul_one _))) -- infer
           have hl: Y.l = a_ μ (a*f)+ a_ μ b:= by rw [←Etick (timesP ha hx) hb]; exact congr_arg (a_ μ) (funext (show ∀ i,((q*P) i).l=(a*f+b) i from fun i=> congr_arg (_+·) (mul_one _)))
           have ht := addedP hv (scaleP (timesP hx hx) u); have hf: a*t=a*g+ u • (a*f*f):= by unfold t p; rw [mul_add, mul_smul_comm, mul_assoc]; -- mul_smul_comm wrong
           have ht:Y.h= (a_ μ (a*g)+u*a_ μ (a*f*f)+a_ μ (b*f)) +a_ μ c:=by
                rw [show Y.h=a_ μ (a*t+b*f+c) from ?_, Etick (addedP (timesP ha ht) (timesP hb hx)) hc,Etick (timesP ha ht) (timesP hb hx),hf,Etick (timesP ha hv) (scaleP (timesP (timesP ha hx) hx) u),show a_ μ (u • (a*f*f))= _ from (show a_ μ (u • (a*f*f))= u*a_ μ (a*f*f) from integral_const_mul ..)]
                exact congr_arg (a_ μ) (funext (show ∀ i,((q*P) i).h= (a*t+b*f+c) i from (fun i=>by change a i*((P i).h)+_+ c i*1= (a i*t i + b i*f i)+ c i; rw [show (P i).h=t i from congr_fun hψ i,mul_one])))
           change Y/X=_; have hx:X.l=a_ μ f:=rfl; rw [JetS.dv]; apply JetS.eta <;> simp only [JetS.ml_s,JetS.ml_l,JetS.ml_h,JetS.sp_l,JetS.sp_s,JetS.sp_h,hs,hY,hX,hx,hl,ht,κ2,κ3,p,u] <;> ring
end Lav
end
end YM.OPE.Borealis

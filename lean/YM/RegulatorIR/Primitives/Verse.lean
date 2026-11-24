import YM.RegulatorIR.Binding.Top

/-! One variable script algebra for local readings and exponent. Fixed cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
open PowerSeries
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{F:E→ℝ}
variable {R:Type}[NormedAddCommGroup R][NormedSpace ℝ R]{f g w:ℝ→ℝ}{T U:ℝ⟦X⟧}

abbrev tale (f:ℝ→ℝ):ℝ⟦X⟧:= Binding.inscription f 1
abbrev Script (s:ℝ⟦X⟧)(f:ℝ→ℝ):Prop:= Aspiration f (term s)

variable (h:ContDiffAt ℝ ∞ f 0)
namespace Script
lemma oneC (c:ℝ): Script (PowerSeries.C c) (fun _=>c):=by
 convert Aspiration.single c 0 using 1
 · simp
 ext i; simp [term,PowerSeries.coeff_C]
lemma add (h:Script T f)(t:Script U g): Script (T+U) (f+g):= by convert Aspiration.add h t using 1;ext; simp [term]
lemma mul (h:Script T f)(t:Script U g): Script (T*U) (f*g):=by
 have hv (u:ℝ⟦X⟧):PowerSeries.mk (term u)=u:= by ext; simp [term];
 have ht:= Aspiration.prod h t; unfold conv at ht; rw [hv,hv] at ht;exact ht
lemma bend (h:Script T f)(he: f =ᶠ[Tested.germ] g): Script T g:=by
 intro i; obtain ⟨c,hc,H⟩:= h i;refine ⟨c,hc,?_⟩;filter_upwards [H,he] with x hx hg; rw [Pi.sub_apply,←hg]; exact hx
include h
lemma actual : Script (tale f) f:=by
 intro i; obtain ⟨δ,c,hd,hc,H⟩:= deposition f i h
 refine ⟨c,hc,?_⟩; filter_upwards [eventually_small hd] with x hx
 have he:= H (1:ℝ) x hx.1 (by simpa using hx.2.le);
 change ‖f x - peval (term _) _ _‖≤_;
 simpa only [term,tale,inscription, PowerSeries.coeff_mk, peval,Zone.eval,smul_eq_mul,mul_one,norm_one, one_pow] using he -- unfolds η?
lemma dictates (d:Script T f):tale f=T:= PowerSeries.ext (fun i=>congr_fun ((actual h).unique d) i)
omit h
lemma predicts_pow (i:ℕ):Script (PowerSeries.X^i) (fun t:ℝ=>t^i):=by convert Aspiration.single (1:ℝ) i <;> simp [term,PowerSeries.coeff_X_pow]
end Script

lemma tale_const (r:ℝ): tale (fun _=>r)=PowerSeries.C r:= Script.dictates contDiffAt_const (Script.oneC r)
lemma lore {φ:E→ℝ}(h:ContDiffAt ℝ ∞ φ 0)(x:E): tale (fun t:ℝ=>φ (t • x))= inscription φ x:=by
 let f':= fun t:ℝ=>φ (t • x)
 have hp: ContDiffAt ℝ ∞ f' 0:= ((show ContDiffAt ℝ ∞ φ ((0:ℝ)• x) from by rwa [zero_smul]).comp 0 (contDiffAt_id.smul contDiffAt_const))
 ext i; rw [tale,inscription,inscription,coeff_mk,coeff_mk,jets_cap φ h,jets_cap f' hp]; simp only [f',smul_eq_mul,mul_one]
lemma tale_eq (h:ContDiffAt ℝ ∞ f 0)(H:g =ᶠ[𝓝 0] f) : tale g=tale f:= Script.dictates (h.congr_of_eventuallyEq H) (Script.bend (Script.actual h) (H.filter_mono nhdsWithin_le_nhds).symm)
lemma tale_jet (i:ℕ): coeff i (tale f)= jet f i 1:=coeff_mk ..
@[simp] lemma tale_base : coeff 0 (tale f)= f 0:= (tale_jet 0).trans (jet_zero ..)
lemma tale_add (h:ContDiffAt ℝ ∞ f 0)(H:ContDiffAt ℝ ∞ g 0):tale (f+g)=tale f+tale g:= Script.dictates (h.add H) (Script.add (Script.actual h) (Script.actual H))
lemma tale_mul (h:ContDiffAt ℝ ∞ f 0)(H:ContDiffAt ℝ ∞ g 0):tale (f*g)=tale f*tale g:= Script.dictates (h.mul H) (Script.mul (Script.actual h) (Script.actual H))
lemma tale_sum {I:Type}(s:Finset I)(f:I→ℝ→ℝ)(h:∀ i∈s,ContDiffAt ℝ ∞ (f i) 0): tale (∑ i∈s,f i)=∑ i∈s,tale (f i):=by
 apply Script.dictates
 · simp_rw [show (∑ i∈s,f i)= _ from funext (fun a=>Finset.sum_apply ..)]; exact ContDiffAt.sum h
 have he:= Aspiration.sum s f _ (fun i hi=>Script.actual (h i hi))
 convert he; ext; simp [term, Finset.sum_apply]
lemma tale_neg (h:ContDiffAt ℝ ∞ f 0):tale (-f)= -tale f:=by rw [← add_left_cancel_iff (a:=tale f), ← tale_add (g:=-f) h h.neg,add_neg_cancel, add_neg_cancel]; rw [show (0:ℝ→ℝ)=fun _=>0 from rfl,tale_const,map_zero]

-- exponent of true germ. alternate stationarity charge by t^2 (free contour scaling)
lemma tale_ex (he:f 0=0)(h:ContDiffAt ℝ ∞ f 0) : tale (fun t=>Real.exp (f t))=expo (tale f):=by
 let G (t:ℝ):= -(t^2*f t)
 let g:=fun t=>Real.exp (f t)
 have H: ContDiffAt ℝ ∞ G 0:= ((contDiffAt_id.pow 2).mul h).neg
 have hf:tale G=-(PowerSeries.X^2*tale f):=by rw [show G= -((fun t:ℝ=>t^2)*f) from rfl, tale_neg (f:=(fun t:ℝ=>t^2)*f) ((contDiffAt_id.pow _).mul h), tale_mul (f:=fun t:ℝ=>t^2) (contDiffAt_id.pow _) h, Script.dictates (f:=fun t:ℝ=> t^2) (contDiffAt_id.pow _) (Script.predicts_pow _)]
 have ht(i:ℕ):jet G (i+2) 1= -(coeff i (tale f)):=by rw [← tale_jet,hf,map_neg,coeff_X_pow_mul', if_pos (by omega),show _ -2=i by omega]
 have hz:jet G 2 1=0:=by rw [show jet G 2 1= _ from ht 0,tale_base,he,neg_zero]
 have hs:Stationary G:=by
    refine ⟨H,?_,?_⟩; simp [G]
    intro u; rw [show u=u • (1:ℝ) by simp,jet_smul,← tale_jet,hf,map_neg,coeff_X_pow_mul', if_neg (by decide),neg_zero,mul_zero]
 have heq: logread G 1=tale f:=by
    ext i; rw [logread, coeff_mk,layers,hz,ht i]; simp
 have hh : PowerSeries.mk (fun i=>normTerm (1:ℝ→ℝ) G i 1)=expo (tale f):=by rw [prints,heq, hz]; simp only [neg_zero,Real.exp_zero,map_one,one_mul];rw [show (1:ℝ→ℝ)=fun _=>1 from rfl, ink_one]; simp
 have ho:=Binding.aspFixed (F:=G) (A:=(1:ℝ→ℝ)) hs contDiffAt_const 1
 refine Script.dictates h.exp (Script.bend (f:=fun t=> projection (1:ℝ→ℝ) G t 1) ?_ ?_)
 · intro n; convert ho n using 1; ext t; simp [peval,Zone.eval, ← hh,term]
 filter_upwards [Tested.eventually_pos] with t ht; rw [projection_eq]; simp [G,mul_div_cancel_left₀ _ (pow_ne_zero _ ht.ne')]
end YM.RegulatorIR.Prim

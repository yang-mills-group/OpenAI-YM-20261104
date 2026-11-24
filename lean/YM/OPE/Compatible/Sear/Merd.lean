import YM.OPE.Compatible.Sear.Stain
/-! # ζ-valuation.Token arithmetic -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {I:Type*}{s t c:ℝ}{i j k:ℕ}{T d:I→ℝ}{l:Filter I}
open PertExtension Series Libra GaussianScore Jargon
section
local notation "J"=> Token
lemma turnC (p q:J)(s:ℝ): p.atK s * q.atK s-(p*q).atK s=s^3 * (p.l*q.h+p.h*q.l)+s^4*(p.h*q.h):=by simp only [JetS.atK,JetS.ml_s,JetS.ml_l,JetS.ml_h,smul_eq_mul]; ring
-- clock Φ eventual.En.
local notation "W"=> RateLE l T
abbrev Feast (p:I→Token)(l:Filter I)(T:I→ℝ):Prop:= RateLE l T (fun i=>(p i).s) 0∧ RateLE l T (fun i=>(p i).l) 0∧ RateLE l T (fun i=>(p i).h) 0
lemma fest {p q:I→Token}(hp:Feast p l T)(h:Feast q l T)(hT:Tendsto T l atTop): Feast (p*q) l T:=by
       let f:= hp.1; let g:= hp.2.1; let k:=hp.2.2; let t:= h.1; let s:=h.2.1; let u:=h.2.2; refine ⟨?_,?_,?_⟩
       · exact (f.mul t).mono (le_of_eq (zero_add _))
       · exact ((f.mul s).add (g.mul t) hT).mono (le_of_eq (zero_add _))
       exact (((f.mul u).add (g.mul s) hT).add (k.mul t) hT).mono (le_of_eq (zero_add _))
lemma revD {p:I→Token}(h:Feast p l T)(hT:Tendsto T l atTop)(he:∀ᶠ i in l,(p i).s=1): Feast (fun i=>(p i)⁻¹) l T:=by
        refine ⟨(RateLE.const 1 hT).congr (he.mono fun i hi=>by simp [hi]),h.2.1.neg.congr (he.mono fun i hi=>by simp [hi]),?_⟩; refine ((((h.2.1.pow 2 hT).mono (le_of_eq (mul_zero _))).sub h.2.2 hT).congr (he.mono fun i hi=>?_)); dsimp only; rw [JetS.sp_h,hi]; simp
variable {A P:I→ Token}
lemma lampFee (h:Feast A l T)(hT:Tendsto T l atTop)(he:RateLE l T d 0): RateLE l T (fun i=>(A i).atK (d i)) 0:= (h.1.add ((he.mul h.2.1).mono (le_of_eq (zero_add _))) hT).add (((he.pow 2 hT).mul h.2.2).mono (le_of_eq (by ring))) hT
lemma shiftP (h: Feast A l T)(hp:Feast P l T)(hd:RateLE l T d s)(hs:s ≤ 0)(ht:Tendsto T l atTop): W (fun i=>(A i).atK (d i)*(P i).atK (d i)-(A i*P i).atK (d i)) (3*s):=by
       simp_rw [turnC]; have hv :=(h.2.1.mul hp.2.2).add (h.2.2.mul hp.2.1) ht
       apply RateLE.add _ _ ht
       · refine ((hd.pow 3 ht).mul hv).mono (le_of_eq ?_); norm_num
       refine ((hd.pow 4 ht).mul (h.2.2.mul hp.2.2)).mono ?_; push_cast; linarith
variable {f g:I→ℝ}
lemma phase_end (h:Feast A l T)(hp:Feast P l T)(hv:∀ᶠ i in l,(A i).s=1)(hT:Tendsto T l atTop)(hs:s<0)(hd: W d s)(hr:3*s ≤ t)(ht:t<0)
 (hF: W (fun i=> f i-(A i).atK (d i)) t) (hG:W (fun i=> g i-(P i).atK (d i)) t):
      Tendsto f l (𝓝 1) ∧ W (fun i=> g i/f i-(P i/A i).atK (d i)) t :=by
          let μ(i):= (A i).atK (d i); have he:Tendsto μ l (𝓝 1):=by
             have h0: (fun i=>(A i).s)=ᶠ[l] (fun i=>1):=hv; have hx:= hd.mul h.2.1|>.tends (by rwa[add_zero]) hT; have hp':= hd.pow 2 hT|>.mul h.2.2|>.tends (by push_cast;linarith) hT
             have hy:= ((tendsto_const_nhds.congr' h0.symm).add hx).add hp'; rw [add_zero,add_zero] at hy; exact hy
          have ha:Tendsto f l (𝓝 1):=by
             convert! ((hF.tends ht hT).add he) using 1
             · funext i; unfold μ; ring
             rw [zero_add]
          let v(i):= P i / A i; let y(i):=(v i).atK (d i); have hy: Feast v l T:= fest hp (revD h hT hv) hT -- implicit
          have hx:= (hG.sub ((hF.mul (lampFee hy hT (hd.mono hs.le))).mono (le_of_eq (add_zero _))) hT).sub ((shiftP h hy hd hs.le hT).mono hr) hT; have hP: W (fun i=>g i-f i*y i) t:=by
              refine RateLE.congr hx ?_; filter_upwards [hv] with i hi; have he:A i*v i=P i:=by unfold v; rw [JetS.dv,mul_left_comm, mul_comm _ ((A i)⁻¹), JetS.uniting (p:=A i) (by rw[hi]; exact one_ne_zero),mul_one]
              rw [he]; unfold y;ring
          refine ⟨ha,RateLE.congr ((hP.mul (RateLE.absBound (2:ℝ) (F:=fun i=>(f i)⁻¹) hT ?_)).mono (le_of_eq (add_zero _))) ?_⟩
          · have ht:= (ha.inv₀ (by norm_num)).norm; rw [inv_one,norm_one] at ht; exact ht.eventually (ge_mem_nhds (by norm_num:(1:ℝ)< 2))
          filter_upwards [ha.eventually (lt_mem_nhds (by norm_num:(1:ℝ)>0))] with i h; unfold y v; change 0<f i at h; field_simp
end
end YM.OPE.Cinders

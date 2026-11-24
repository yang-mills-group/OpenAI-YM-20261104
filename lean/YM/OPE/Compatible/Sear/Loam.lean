import YM.OPE.Compatible.Sear.Axe
/-!
# normalization under clock L1 receipts -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {I:Type*}{s t c:ℝ}{i j k:ℕ}{T d:I→ℝ}{l:Filter I}
open PertExtension Series Libra GaussianScore Jargon
variable {X:I→Type*}[∀ i,MeasurableSpace (X i)] {S:∀ i,Set (X i)} {μ:∀ i,Measure (X i)}
variable [∀ i,IsProbabilityMeasure (μ i)] {P Q:Hang X}{p q:PayR X}
omit [∀ i,IsProbabilityMeasure (μ i)] in
def Butte (μ:∀ i,Measure (X i))(l:Filter I)(T:I→ℝ)(P:Hang X):Prop:=∀ i:Fin 3, Grain μ l T (run_H P i.val) 0
abbrev propH (μ:∀ i,Measure (X i))(p:Hang X)(i:I):Token:= ⟨∫ x,(p i x).s ∂μ i,∫ x,(p i x).l ∂μ i,∫ x,(p i x).h ∂μ i⟩
lemma props (h:Butte μ l T P)(hp:Tendsto T l atTop)(hd:RateLE l T d 0): Feast (propH μ P) l T ∧ Grain μ l T (aftD P d) 0 ∧ ∀ᶠ i in l, (∫ x,aftD P d i x ∂μ i) = (propH μ P i).atK (d i):=by
      have hX:=h 0; have hY:=h 1; have hZ:= h 2; refine ⟨⟨hX.integral.2,hY.integral.2,hZ.integral.2⟩,?_,?_⟩
      · exact ((hX.add ((Grain.const hd|>.mul hY).mint (le_of_eq (zero_add _))) hp).add ((Grain.const (hd.pow 2 hp)|>.mul hZ).mint (by norm_num)) hp)
      filter_upwards [hX.integral.1,hY.integral.1,hZ.integral.1] with i hi hK hH; let v:=μ i; let p(x):=(P i x).s; let f(x):=(P i x).l; let g(x):=(P i x).h; let t:=d i; have he: Integrable p v:=hi; have hh: Integrable f v:=hK; have hz: Integrable g v:=hH; change (∫ x,p x+t*f x+t^2*g x ∂v)= (∫ x,p x ∂v) + t*(∫ x,f x ∂v)+ t^2* ∫ x,g x ∂v; rw [integral_add (show Integrable (fun x=>p x+t*f x) v from he.add (hh.const_mul t)) (hz.const_mul (t^2)), integral_add he (hh.const_mul t),integral_const_mul,integral_const_mul]
omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma gluing (h:Butte μ l T P)(hv:Butte μ l T Q)(ht:Tendsto T l atTop): Butte μ l T (P*Q):=by
      have hX:=h 0; have hY:=h 1; have hZ:= h 2; have he:=hv 0; have h1:=hv 1; have h2:=hv 2; intro i; fin_cases i
      · exact (hX.mul he).mint (le_of_eq (zero_add _))
      · exact (((hX.mul h1).add (hY.mul he) ht).mint (le_of_eq (zero_add _)))
      exact (((hX.mul h2).add (hY.mul h1) ht).add (hZ.mul he) ht).mint (le_of_eq (zero_add _))
def SmoothD (μ:∀ i,Measure (X i))(l:Filter I)(S:∀ i,Set (X i))(p:PayR X):Prop:=∀ᶠ i in l,AEStronglyMeasurable ((S i).indicator (p i)) (μ i)
variable (hS:∀ᶠ i in l,MeasurableSet (S i))(hμ:∀ v:ℝ,RateLE l T (fun i=> (μ i).real (S i)ᶜ) v)
include hS hμ
lemma View (hp:Playbook S l T P d p t)(hv:Butte μ l T P)(ht:Tendsto T l atTop)(hd:RateLE l T d 0)(hX:SmoothD μ l S p): RateLE l T (fun i=>(∫ x in S i,p i x ∂μ i)-(propH μ P i).atK (d i)) t :=by
      obtain ⟨hh,h,H⟩:= props hv ht hd; let f:=aftD P d; let a:PayR X:=fun i=> (S i).indicator (p i); let b:PayR X:=fun i=> (S i).indicator (f i); let v:=a-b; let q:= p-aftD P d; have hm(i:I): v i=(S i).indicator (q i):=by ext x; change a i x-b i x=_; by_cases h:x∈S i<;> simp only[a,b,q,f,indicator_of_mem,h,indicator_of_notMem,Pi.sub_apply,not_false_eq_true,sub_self]
      have hg: Grain μ l T v t:= by
           refine (Large.crop hS hp.wears ?_).shift (Eventually.of_forall fun i=>(hm i).symm); filter_upwards [hS,hX,h.integral.1] with i hi he hI
           rw [← hm]; exact he.sub (hI.1.indicator hi)
      have hh:=hg.integral; have hp:= h.integral; let F(i):= ∫ x,v i x ∂μ i; let G(i):= (∫ x in S i,f i x ∂μ i)-(∫ x,f i x ∂μ i); refine RateLE.congr (F:=fun i=> F i+G i) (hh.2.add (missingI _ _ hS hμ ht h t) ht) ?_; filter_upwards [H,hp.1,hh.1,hS] with i hi hk hl hS; let v':= μ i; let V:S i ⊆ S i:=Subset.rfl; have hb:Integrable (b i) (μ i):=hk.indicator hS; have hf:Integrable (a i) (μ i):=by rw[show a i=v i+b i from by unfold v; simp]; exact hl.add hb
      unfold F v; simp only [Pi.sub_apply]; rw [integral_sub hf hb, ←hi, ←integral_indicator hS (μ:=μ i) (f:=p i)]; unfold G b a; rw[integral_indicator hS (μ:=μ i) (f:=f i)]; unfold f;ring
lemma finalV (ht:Tendsto T l atTop)(hp:Playbook S l T P d p t)(hv:Playbook S l T Q d q t)(h:Butte μ l T P)(hr:Butte μ l T Q)(hd:RateLE l T d s)(he:s<0)(h3:3*s ≤ t)(hz:t<0)(hP:∀ᶠ i in l,(propH μ P i).s=1)
 (hs:SmoothD μ l S p)(hq:SmoothD μ l S (p*q)): RateLE l T (fun i=>(∫ x in S i,p i x*q i x ∂μ i)/(∫ x in S i,p i x ∂μ i)-(propH μ (P*Q) i/propH μ P i).atK (d i)) t :=by
         have hu:= rested hp hv hd he hz ((mul_comm s 3).symm ▸ h3) ht; let T':= d; have hA:= hd.mono he.le; have hh:= gluing h hr ht; exact (phase_end (props h ht hA).1 (props hh ht hA).1 hP ht he hd h3 hz (View hS hμ hp h ht hA hs) (View hS hμ hu hh ht hA hq)).2
end YM.OPE.Cinders

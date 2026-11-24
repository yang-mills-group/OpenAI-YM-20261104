import YM.FVA2.WickView

/-!
# Primitive `rise` ↔ exponentiated towers in the same coupling clock
Shed estimates only used for Taylor algebra on rays. Not claiming decoupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.ExactTower
open Filter Topology Set PowerSeries
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.StationaryMarks
open GaussianScore MeasureTheory
open MeasureTheory.Measure (IsAddHaarMeasure)
open scoped Topology Classical ContDiff
variable {E A I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]

local notation "fr" => fun c:ℝ=>(fun _:E=>c)
local notation "𝔼" => ℕ→ℝ

lemma up_add {x y:E→ℝ}(h:ContDiffAt ℝ ∞ x 0)(hp:ContDiffAt ℝ ∞ y 0): rise (x+y)=rise x+rise y:= by
    apply Stack.into; intro u; apply PowerSeries.ext; intro k; rw [map_add,map_add]; simp_rw [read_rise]; exact congr_fun ((directions (h.add hp) u).unique ((directions h u).add (directions hp u))) k
lemma rise_cash (r:ℝ): rise ((fr) r)=roll r := by
    apply PowerSeries.ext; intro n; apply Subtype.ext; funext x; rw [← reading_term, ← reading_term,read_rise,rollThrough]; rcases n with _|n <;> simp [jet,iteratedFDeriv_const_of_ne] -- reference.E
lemma rise_local {f g:E→ℝ}(h:f=ᶠ[𝓝 0] g): rise f=rise g:= by
    apply PowerSeries.ext; intro n; apply Subtype.ext; rw [rise,rise,coeff_mk,coeff_mk]; ext1 x; change jet f n x=jet g n x; unfold jet; rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h n).eq_of_nhds]
lemma up_zero : rise (0:E→ℝ)=0:= (rise_cash (0:ℝ)).trans (by unfold roll;rw [map_zero,map_zero])
lemma rose (f:E→ℝ) : constantCoeff (rise f)=algebraMap ℝ (Permit E) (f 0):= by
    rw [rise,constantCoeff_mk]; exact Subtype.ext (funext (jet_zero f))
lemma rose_zero {f:E→ℝ}(h:f 0=0): constantCoeff (rise f)=0:=by rw [rose,h,map_zero]
lemma rise_natural (r:ℝ){f:E→ℝ}(h:ContDiffAt ℝ ∞ f 0): rise (r • f)= roll r * rise f:= by rw [ show r • f = ((fr) r)*f from rfl, rise_mul (hf:= (show ContDiffAt ℝ ∞ ((fr) r) 0 from contDiffAt_const)) h,rise_cash] -- rw defeq
lemma rise_weight {f:I→E→ℝ}(s:Finset I)(h:∀ i∈s,ContDiffAt ℝ ∞ (f i) 0): rise (∑ i∈s,f i)=∑ i∈s,rise (f i):= by
   induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty,Finset.sum_empty,up_zero]| insert i s hi ih=> have he:=fun j hj=> h j (Finset.mem_insert_of_mem hj); rw [Finset.sum_insert hi,Finset.sum_insert hi,up_add (h _ (by simp)) (f'? s he), ih he] -- need scope
where f'? (s:Finset I)(h:∀ i∈s,ContDiffAt ℝ ∞ (f i) 0): ContDiffAt ℝ ∞ (∑ i∈s,f i) 0:= by rw [ show ∑ i∈s,f i=fun x=>∑ i∈s,f i x from funext (fun x=> Finset.sum_apply ..) ]; exact ContDiffAt.sum h
omit [FiniteDimensional ℝ E] in
lemma risen (f:I→E→ℝ)(s:Finset I)(h:∀ i∈s,ContDiffAt ℝ ∞ (f i) 0): ContDiffAt ℝ ∞ (∏ i∈s,f i) 0 := by induction s using Finset.induction_on with| empty=> rw [Finset.prod_empty]; exact contDiffAt_const | insert i s hi ih=> rw [Finset.prod_insert hi]; exact ContDiffAt.mul (h i (by simp)) (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
lemma rising {f:I→E→ℝ}(s:Finset I)(h:∀ i∈s,ContDiffAt ℝ ∞ (f i) 0): rise (∏ i∈s,f i)=∏ i∈s,rise (f i):= by
   induction s using Finset.induction_on with| empty=> rw [Finset.prod_empty,Finset.prod_empty,rise_one]| insert i s hi ih=> have he:=fun j hj=> h j (Finset.mem_insert_of_mem hj); rw [Finset.prod_insert hi,Finset.prod_insert hi,rise_mul (h _ (by simp)) (risen f s he), ih he]
lemma rise_pow {f:E→ℝ}(h:ContDiffAt ℝ ∞ f 0)(k:ℕ): rise (f^k)= (rise f)^k:= by induction k with| zero=>rw [pow_zero,pow_zero,rise_one] | succ k ih=> rw [pow_succ,pow_succ,rise_mul (f:=f^k) (h.pow k) h,ih]

lemma locked (f:E→ℝ)(F:Matrix I I (E→ℝ)) [Fintype I][DecidableEq I] (h:∀ i j,ContDiffAt ℝ ∞ (F i j) 0) (hf:f=F.det) : (F.map rise).det=rise f:= by
    let G(σ: Equiv.Perm I) := ∏ i,F (σ i) i; let c(σ:Equiv.Perm I):ℤ:=Equiv.Perm.sign σ; subst f
    have he(σ:Equiv.Perm I): ContDiffAt ℝ ∞ (c σ • G σ) 0:= by
        rw [← show ((c σ:ℤ):ℝ) • G σ = c σ • G σ from Int.cast_smul_eq_zsmul ..]; exact (risen _ Finset.univ (fun i _=>h (σ i) i)).const_smul ((c σ:ℤ):ℝ)
    have hr(σ:Equiv.Perm I): roll (E:=E) ((c σ:ℤ):ℝ) = (c σ: Ticket E):= by unfold roll; rw [map_intCast,map_intCast]
    rw [Matrix.det_apply, Matrix.det_apply]; change _=rise (∑ σ,c σ • G σ); rw [rise_weight _ (fun i _=> he i)]; symm; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ ← show ((c i:ℤ):ℝ) • G i = c i • G i from Int.cast_smul_eq_zsmul .., rise_natural _ (risen _ _ (fun p _=>h (i p) p)), hr]; rw [← zsmul_eq_mul,rising _ (fun p _=>h (i p) p)]; rfl

section exp
open Tested
local notation "EX" => Survey.referenceCharge
local notation "rz"=>fun n:ℕ=>(Nat.factorial n:ℝ)⁻¹
variable {f:E→ℝ}(h:ContDiffAt ℝ ∞ f 0)(hz:f 0=0)
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma polar (k:ℕ): EX k ∘ f=∑ i∈Finset.range (k+1), (rz) i • f^i:= by funext x; rw [Finset.sum_apply]; unfold Function.comp; unfold Survey.referenceCharge; apply Finset.sum_congr rfl; intro i _; rw [Pi.smul_apply, Pi.pow_apply,smul_eq_mul]; ring
include h
lemma badge (k:ℕ) : rise (EX k ∘ f)=∑ i∈Finset.range (k+1),roll ((rz) i)*(rise f)^i:= by rw [polar, rise_weight (f:=fun i=>(rz) i • f^i) _ (fun i _=> (h.pow i).const_smul ((rz) i))]; simp_rw [ rise_natural (f:=f^_) _ (h.pow _), rise_pow h ]
omit [FiniteDimensional ℝ E] in
lemma bade (k:ℕ) : ContDiffAt ℝ ∞ (EX k ∘ f) 0:= by rw [polar]; exact rise_weight.f'? _ (fun i _=> (h.pow i).const_smul ((rz) i)) -- private?
include hz
lemma receive (k:ℕ)(x:E) : Bill (k+1) (fun t=> Real.exp (f (t•x))- EX k (f (t•x))) := by
    obtain ⟨C,hC,h⟩:= directions h x 0
    refine ⟨ C^(k+1)*Real.exp C, by positivity,?_⟩
    filter_upwards [h,eventually_small (show (0:ℝ)<1 from zero_lt_one)] with t ht hh
    have hp : ‖f (t•x)‖ ≤ C*t:= by simpa [peval,Zone.eval,hz] using ht
    have hb : ‖f (t•x)‖ ≤ C := hp.trans (mul_le_of_le_one_right hC hh.2.le)
    calc
       _ ≤ ‖f (t•x)‖^(k+1) * Real.exp ‖f (t•x)‖ := Shed.expJuice _ _
       _ ≤ (C*t)^(k+1) * Real.exp C := by have hl:=hh.1; gcongr
       _ = _:= by rw [mul_pow]; ring
lemma rice : exponential (rise f)= rise (Real.exp ∘ f):= by
    let V := exponential (rise f); apply Stack.into; intro x
    let F:=fun t:ℝ=>Real.exp (f (t•x)); suffices hh: Aspiration F (term (Stack.read x V)) from PowerSeries.ext fun k=>Eq.trans (congr_fun (hh.unique (directions h.exp x)) k) (read_rise x _ _).symm
    intro k
    have ht(i:ℕ)(he:i∈Finset.range (k+1)): jet (EX k ∘ f) i x= term (Stack.read x V) i:= by rw [← read_rise,term, reading_term,reading_term,badge h]; exact congr_fun (congr_arg Subtype.val (acting (rose_zero hz) k i (by rw [Finset.mem_range] at he; omega))) x |>.symm
    let P:=EX k ∘ f
    have ht'(t:ℝ): peval (fun i=>jet P i x) k t = peval (term (Stack.read x V)) k t:= Finset.sum_congr rfl (fun i hi=> congr_arg (t^i • ·) (ht i hi))
    obtain he:= directions (bade h k) x k
    rw [funext ht'] at he
    have hx: F-peval (term (Stack.read x V)) k = (fun t=> F t - P (t•x))+ ((fun t=> P (t • x))- peval (term (Stack.read x V)) k) := by funext t; dsimp only [Pi.add_apply,Pi.sub_apply]; abel
    rw [hx]; exact bill_add (receive h hz k x) he
end exp
variable (e:A→E)(p:MS.Koszul.Sector A)(he:∀ i,p i=true→e i=0)
theorem blossom (f:PowerSeries (Permit E)) : Boson.sharp e p he (Stack.exponential f)=Paper.exp (Boson.sharp e p he f):= by
    let P:=Boson.sharp e p he; let B:=Boson.billInk e p he; let K:=Paper.rex (P f); have he' (t:ℝ): P (roll t)= PowerSeries.C (algebraMap ℂ (↥(MS.Theater.Dark p)) (t:ℂ)):= by
        unfold P Boson.sharp roll; rw [ PowerSeries.map_C ]; apply congr_arg; apply Subtype.ext; rw [ MS.Theater.cash1 ]; exact MS.Cylinder.Taylor.ink_const _ _
    apply PowerSeries.ext; intro n
    rw [Boson.sharp, coeff_map, exponential,coeff_mk,Paper.exp,coeff_mk]; change B _=coeff n (K n)
    rw [ show B (PowerSeries.coeff n (∑ i∈Finset.range (n+1),Stack.roll ((i.factorial:ℝ)⁻¹)* f^i))= _ from (PowerSeries.coeff_map B _ _).symm]; change coeff n (P _)=_; unfold K Paper.rex; simp_rw [ map_sum,map_mul,map_pow,he',coeff_smul,coeff_C_mul,MS.Puff.Actors.phase ]; push_cast; simp_rw [ ← Algebra.smul_def ]

variable [MeasurableSpace E][BorelSpace E] (Γ: Law E)(μ: Measure E)[IsAddHaarMeasure μ]
def capital := ∫ x:E, Γ.kern x ∂μ
lemma venture : 0<capital Γ μ:= Splice.positive Γ μ
lemma ticketed (S:E→ℝ)(h: kernel S=Γ.kern) (f:E→ℝ):
    C (capital Γ μ) * input Γ μ ( rise f * exponential (advancing S)) = PowerSeries.mk ( Radial.moment μ f S) := by
    let A:=rise f* exponential (advancing S); have he(i:ℕ)(x:E): (coeff i A).val x=integrandSeries S f i x:= by
         unfold A; rw [← reading_term,map_mul,coeff_mul,integrandSeries,Zone.mul]; exact Finset.sum_congr rfl fun j _=> by rw [read_rise,business S]
    have hv:= (venture Γ μ).ne'; apply PowerSeries.ext; intro n; rw [coeff_mk,coeff_C_mul,moment]; simp_rw [normTerm,h,← he]
    unfold input throughPrice; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_mk,LinearMap.toAddMonoidHom_coe]; change capital Γ μ * ((∫ x, (coeff n A).val x*Γ.kern x ∂μ)/(capital Γ μ)) = _; field_simp
end YM.FVA2.ExactTower

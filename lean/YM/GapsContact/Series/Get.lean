import YM.GapsContact.Series.River
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Vandermonde
/-!
# Comparison currency: kth coefficient from actual Euclidean asymptotic vs same labels holomorphic,
# costs by k NOT by extrapolation/truncation order n
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Pattern
open Function Filter Set Metric Complex Matrix
open scoped Topology BigOperators ContDiff Classical Matrix
variable {ι Ω E:Type*}{T:Type}

lemma TagPrice.several (f:Filter Ω)(A:ι→Ω→E→ℂ)(s:Finset ι) {S:Set E}{p:Ω→ℝ}
     (h:∀ i∈s,TagPrice f (A i) S p) :TagPrice f (fun v x=>∑ i∈s,A i v x) S p:=by
   induction s using Finset.induction_on with
   | empty=>exact ⟨0,le_rfl,Eventually.of_forall fun _ _ _=>by simp⟩
   | insert z s hz ih => simpa only [Finset.sum_insert hz] using (h z (Finset.mem_insert_self ..)).add (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
lemma TagPrice.pays {f: Filter Ω}{K:Set E}{F:Ω→E→ℂ}{G:Ω→ℂ}{u v:Ω→ ℝ}
   {C:ℝ}(h:TagPrice f F K u)(hc: 0≤C) (hu:∀ᶠ i in f, ‖G i‖ ≤ C*v i) : TagPrice f (fun i x=> G i*F i x) K (fun i=> u i*v i):=by
   obtain ⟨D,hD,h⟩:=h; refine ⟨D*C,by positivity,?_⟩; filter_upwards [hu,h] with i hi hh x hx
   rw [norm_mul]; exact (mul_le_mul hi (hh x hx) (norm_nonneg _) ((norm_nonneg _).trans hi)).trans_eq (by ring)
lemma TagPrice.at {f:Filter Ω}{K:Set E}{F:Ω→E→ℂ}{u:Ω→ℝ} (h:TagPrice f F K u){g:Filter ι}{σ:ι→Ω}(hσ:Tendsto σ g f) : TagPrice g (fun i x=> F (σ i) x) K (fun i=> u (σ i)):=by
   obtain ⟨C,hC,h⟩:=h; exact ⟨C,hC,hσ.eventually h⟩
lemma TagPrice.improve {u v:Ω→ℝ}{f: Filter Ω}{K:Set E}{F:Ω→E→ℂ}(h:TagPrice f F K u) {C:ℝ}(hc:0≤C) (hu:∀ᶠ i in f,u i ≤ C*v i) :TagPrice f F K v:=by
   obtain ⟨D,hD,h⟩:=h; exact ⟨D*C,by positivity,(h.and hu).mono fun _ h x hx=>(h.1 x hx).trans ((mul_le_mul_of_nonneg_left h.2 hD).trans_eq (mul_assoc ..).symm)⟩

variable (f:Filter Ω)(p:Ω→ℝ)
structure Meter (f:Filter Ω)(p:Ω→ℝ) where
   σ : ℕ → Ω
   pegs : Tendsto σ atTop f
   label : ℝ
   held : 0 < label
   goes : Tendsto (fun i=> p (σ i)/wage i) atTop (𝓝 label)
   little : Tendsto p f (𝓝 0)
   warm : ∀ᶠ i in f,0<p i
variable {f p} (H:Meter f p)
include H in
lemma Meter.short :∀ᶠ i in f,p i∈ Ioc (0:ℝ) 1:=H.warm.and (H.little.eventually_le_const zero_lt_one) -- include?

abbrev recv (k b : ℕ) := H.σ (k+b)
variable {H}
lemma roll (H:Meter f p)(a:ℕ): Tendsto (fun i : ℕ=>recv H i a) atTop f:=H.pegs.comp (tendsto_add_atTop_nat a)

lemma levels (H:Meter f p)(a:ℕ): Tendsto (fun i=> p (recv H i a) / wage i) atTop (𝓝 (H.label*wage a)):=by
   apply ((H.goes.comp (tendsto_add_atTop_nat a)).mul_const (wage a)).congr
   intro i; change p (recv H i a) / wage (i+a)*wage a=_; rw [wage_add]; field_simp [(wage_pos i).ne',(wage_pos a).ne']
lemma own_levels (H:Meter f p) (j:ℕ) : (∃ C:ℝ, 0≤C ∧ ∀ᶠ i:ℕ in atTop, p (recv H i j) ≤ C*wage i) ∧ ∃ C:ℝ,0≤C ∧ ∀ᶠ i:ℕ in atTop,(p (recv H i j))⁻¹ ≤ C*(wage i)⁻¹:=by
   let c:= H.label*wage j; have hc:0<c:=mul_pos H.held (wage_pos _); have h:= levels H j
   refine ⟨⟨c+1,by positivity,(h.eventually_le_const (lt_add_one _)).mono fun n h=> (div_le_iff₀ (wage_pos _)).mp h⟩,(c/2)⁻¹,by positivity,?_⟩
   filter_upwards [h.eventually_const_le (half_lt_self hc)] with n hn
   have hh:= (le_div_iff₀ (wage_pos _)).mp hn
   rw [← mul_inv]; exact inv_anti₀ (mul_pos (half_pos hc) (wage_pos _)) hh
namespace Meter
variable (H)
def basis (q n:ℕ) : Matrix (Fin q) (Fin q) ℂ := Matrix.vandermonde (fun j=> ↑(p (recv H n j) / wage n))
lemma invert (q:ℕ) : ∃ B: Matrix (Fin q) (Fin q) ℂ, Tendsto (fun n=> (basis H q n)⁻¹) atTop (𝓝 B) ∧ ∀ᶠ n in atTop,(basis H q n)⁻¹*basis H q n=1:=by
   let p:= fun j:Fin q=> H.label * wage (j:ℕ); let A:=Matrix.vandermonde (fun j:Fin q=> (p j:ℂ))
   have hh : Tendsto (fun n=>basis H q n) atTop (𝓝 A):= by
      apply tendsto_pi_nhds.mpr; intro j; apply tendsto_pi_nhds.mpr; intro k; exact ((Complex.continuous_ofReal.continuousAt.tendsto.comp (levels H j)).pow k.val)
   have hx:A.det ≠ 0:=by
      apply Matrix.det_vandermonde_ne_zero_iff.mpr
      suffices h: StrictAnti p from Complex.ofReal_injective.comp h.injective
      apply (show StrictAnti ((fun n:ℕ => H.label * wage n) ∘ (fun i: Fin q=> i.val)) from StrictAnti.comp_strictMono _ (Fin.val_strictMono))
      apply strictAnti_nat_of_succ_lt; intro i; apply mul_lt_mul_of_pos_left _ H.held; rw [wage_add]; apply mul_lt_of_lt_one_right (wage_pos _); norm_num [wage]
   have hp:ContinuousAt (fun x:ℂ=> Ring.inverse x) (A.det):=by rw [show _ from funext (fun x:ℂ=> Ring.inverse_eq_inv x)]; exact continuousAt_inv₀ hx
   refine ⟨A⁻¹,(continuousAt_matrix_inv A hp).tendsto.comp hh,?_⟩
   filter_upwards [ ((continuous_id.matrix_det.tendsto A).comp hh).eventually (eventually_ne_nhds hx)] with n hn
   exact nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hn)

-- linear extraction from q evaluations, use `get n` at order q. defined dummy off k≥q

def rate (j:ℕ)(q n:ℕ)(i:Fin q):ℂ:= if h:j<q then (((basis H q n)⁻¹) ⟨j,h⟩ i) / ↑((wage n)^j) else 0

def pull (j:ℕ)(F:Ω→ E→ ℂ)(q n:ℕ)(x:E):=∑ i:Fin q, rate H j q n i*F (recv H n i) x

lemma fee (j q:ℕ) (i:Fin q): ∃ C:ℝ,0≤C ∧ ∀ᶠ n in atTop, ‖rate H j q n i‖ ≤ C*(wage n)⁻¹^j :=by
   by_cases hx:j<q; swap; exact ⟨0,le_rfl,Eventually.of_forall fun n=> by simp [rate,hx]⟩
   obtain ⟨A,hA,-⟩:= invert H q
   let j':Fin q:=⟨j,hx⟩; let C:= ‖A j' i‖
   have ht:Tendsto (fun n=> ‖(basis H q n)⁻¹ j' i‖) atTop (𝓝 C):= ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA j') i).norm) -- inverse application parentheses issue
   refine ⟨C+1,(by unfold C; positivity),?_⟩
   filter_upwards [ht.eventually_le_const (lt_add_one _)] with n hn; have hx':=wage_pos n; rw [rate,dif_pos hx,norm_div,norm_real,Real.norm_of_nonneg (pow_nonneg (wage_pos n).le _), div_eq_mul_inv, inv_pow]; exact mul_le_mul_of_nonneg_right hn (by positivity)
lemma high_nf (j q:ℕ){S:Set E}{b:ℕ}{F:Ω→ E→ℂ}(h:TagPrice f F S (fun i=> (p i)⁻¹^b)):
     TagPrice atTop (pull H j F q) S (fun i=> (wage i)⁻¹^(b+j)):=by
   apply TagPrice.several atTop (fun k n x=> H.rate j q n k * F (recv H n k) x) Finset.univ; intro k _
   obtain ⟨A,hA,ha⟩:= H.fee j q k; obtain ⟨B,hB,hb⟩:= (own_levels H k).2; have he : TagPrice atTop (fun i x=> F (recv H i k) x) S (fun i=> (wage i)⁻¹^b):=by
      apply (h.at (roll H k)).improve (C:=B^b) (by positivity)
      filter_upwards [hb,(roll H k).eventually H.warm] with i hI hP; rw [← mul_pow]; exact pow_le_pow_left₀ (inv_nonneg.mpr hP.le) hI b
   simpa only [pow_add] using he.pays hA ha
end Meter

def chart (F:ℕ→ E→ℂ)(p:ℂ)(q:ℕ)(x:E):=∑ i:Fin q,p^(i:ℕ)*F i x
lemma chart_next (F:ℕ→E→ℂ)(p:ℂ)(n:ℕ)(x:E) :chart F p (n+1) x= chart F p n x+p^n* F n x:=by rw [chart,Fin.sum_univ_castSucc]; rfl

namespace Meter
variable (H)
lemma right_coeff {k q:ℕ} (hx:k<q) : ∀ᶠ n in atTop, ∀ (F:ℕ→ℂ), (∑ i:Fin q, H.rate k q n i* chart (fun j (_:Unit)=> F j) (↑(p (recv H n i)):ℂ) q ())=F k:=by
   filter_upwards [(invert H q).choose_spec.2] with n hn F
   let A:= fun j:Fin q=> (↑(wage n ^ (j:ℕ)):ℂ) * F j; let Y:=basis H q n
   have ht(i:Fin q): chart (fun j (_:Unit)=>F j) (↑(p (recv H n i)):ℂ) q ()=(Y *ᵥ A) i:=by
      unfold chart; apply Finset.sum_congr rfl; intro j _;
      change (↑(p (recv H n i)):ℂ)^j.val*F j= (↑(p (recv H n i) / wage n):ℂ)^j.val*A j
      have hk: ((↑(wage n):ℂ)) ≠ 0:= Complex.ofReal_ne_zero.mpr (wage_pos _).ne'; unfold A; push_cast; rw [div_pow]; field_simp
   let x:= (⟨k,hx⟩:Fin q); let t:ℂ:= ↑(wage n^k)
   have hp:t≠0:= Complex.ofReal_ne_zero.mpr (pow_pos (wage_pos _) k).ne'
   calc
      _ = t⁻¹* ((Y⁻¹ *ᵥ (Y *ᵥ A)) x):=by
          change _= t⁻¹*(∑ j:Fin q, _ * _); rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [ht i]; unfold rate; rw [dif_pos hx]; change _/t*_=_; ring
      _ = _ :=by rw [mulVec_mulVec, show Y⁻¹*Y=1 from hn, Matrix.one_mulVec]; change t⁻¹*(t*_)=_; field_simp; rfl
end Meter
end YM.GapsContact.Pattern

import YM.Comparison.RG02.Adjacent.Rank
/-!
# Kinetic rescaling convention for the single local step

Takes from the formal prescription a list of kinetic readout coefficients including the zeroth
one `=1`. These are NOT chosen from a read on uncertain actual fields nor even fit via finite-wave
regression on this torus. When going through the zero-momentum operation callers take THE
`ω_e` on their cover/period-limit arrays. `ranking` (binder order i≤r not used; formal symbol extends outside studied orders; on any algebraic functional test such as
suitable weighted evaluation of second directional tensors) specifies the algebraic convention;
the kinetic rescaling annuls all such p_k tests assigned that same value. It is NOT
a proposal to replace symbol readout on constructed regulator by bare Hessian eval. That would
likely even change the conversion! Including whole P derivatives/factorial in the test (k=2 is
λ of ordinary total Hessian, with normalization e.g. λ projected by classical look; sign due
to log negative). `Preserves` delivers parity sufficiency to choose an Even-Caliber; quantitative
long-wave construction & existence on cover belongs RG08 (only Thermal.simple wave theorem here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice Marker Multi
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
local notation "φ"=> 𝓝 (0:ℝ)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
structure Caliber where
 measure : ℕ→ℝ
 starts : measure 0=1
namespace Caliber
variable (p : Caliber) (r:ℕ)
local notation "H"=> p.measure

def tariff (t:ℝ):= ∑ i∈range (r+1), t^i*p.measure i
lemma smooth:ContDiff ℝ ω (p.tariff r):= ContDiff.sum fun _ _=> (contDiff_id.pow _).mul contDiff_const
lemma zero_tariff:p.tariff r 0=1 := by
   unfold tariff; rw [sum_eq_single 0]; rw [pow_zero,p.starts,mul_one]
   · intro i hi he; rw [zero_pow he,zero_mul]
   simp
lemma rates : ∀ᶠ t in φ,0< p.tariff r t:= ( (p.zero_tariff r) ▸ (p.smooth r).continuous.tendsto 0 : Tendsto (p.tariff r) (𝓝 0) (𝓝 1)).eventually (lt_mem_nhds zero_lt_one)

-- canonical gauge of positive coupling chart direct

def direct : UnitCost where
 rating x:= (Real.sqrt (p.tariff r x))⁻¹
 smooth := ((p.smooth r).contDiffAt.sqrt (by simp [p.zero_tariff])).inv (by simp [p.zero_tariff])
 origin:= by simp [p.zero_tariff]
def back : UnitCost:= (p.direct r).inverseCurve
local notation "ζ"=> p.back r
local notation "η"=> p.direct r

theorem income (t:ℝ) (h:0≤ p.tariff r t): ((p.direct r).rating t)⁻¹ ^ 2=p.tariff r t:= by unfold direct; simp only [inv_inv, Real.sq_sqrt h]
theorem real_ratio (t:ℝ) : Integral.temperature ((p.direct r).enter t)= (if 0≤ p.tariff r t then Integral.temperature t * p.tariff r t else 0):= by
   split
   next h=> rw [Integral.temperature,UnitCost.enter,mul_pow,mul_inv,← p.income r t h]; simp [Integral.temperature]
   next h=> simp [UnitCost.enter, Integral.temperature,direct, Real.sqrt_eq_zero_of_nonpos (le_of_lt (lt_of_not_ge h))]

def EvenK: Prop:= ∀ i≤r, Odd i→p.measure i=0
variable (he : p.EvenK r)
lemma even_direct (h: p.EvenK r): (p.direct r).Even:= Eventually.of_forall fun x=> by
      have he:p.tariff r (-x)=p.tariff r x:= Finset.sum_congr rfl fun i hi=>by
           rcases Nat.even_or_odd i with h₀|h₀
           · rw [h₀.neg_pow]
           rw [h _ (mem_range_succ_iff.mp hi) h₀]; simp
      unfold direct; dsimp only; rw [he]
lemma even_back (h:p.EvenK r): (p.back r).Even:= UnitCost.Recurs.even _ _ (p.direct r).rightInverse (p.even_direct r h)
lemma forward_back: UnitCost.Recurs (p.direct r) (p.back r):= (p.direct r).rightInverse
private lemma owes (i:ℕ)(t:ℝ) : (money ζ 0 i 2 t)=(↑((p.back r).rating t)⁻¹:ℂ)^2 * (↑((p.back r).enter t):ℂ)^i:= by unfold money UnitCost.enter tags; rw [zpow_zero]; push_cast; ring
lemma scale_pred : ∀ᶠ x in φ,(∑ i∈ range (r+1), (p.measure i:ℂ)*money ζ 0 i 2 x)=1:= by
   have hB:= (p.back r).roots.eventually (p.rates r)
   filter_upwards [hB,(p.forward_back r).symm.stays,(p.back r).bright] with x ht he hx
   let w:= (p.back r).rating x; let t:= (p.back r).enter x
   have hz : (((p.measure 0):ℝ) : ℂ)=1 := by simp [p.starts] -- not actually needed
   have hp: p.tariff r t=w^2:= by rw [← p.income r t ht.le,he,inv_inv]
   calc
     _ = (↑w:ℂ)⁻¹ ^ 2 * (↑(p.tariff r t):ℂ) := by
        unfold tariff; push_cast; rw [mul_sum]; apply sum_congr rfl; intro i hi; rw [owes]; unfold w t; push_cast; ring
     _=1:=by rw [hp,Complex.ofReal_pow, ← mul_pow,inv_mul_cancel₀ (show (↑w:ℂ) ≠0 from Complex.ofReal_ne_zero.mpr hx.ne'),one_pow]
lemma horizon (v:ℕ) : (∑ i∈range (r+1),motion (money (p.back r) 0 i 2) v*(p.measure i:ℂ))=if v=0 then 1 else 0:= by
   have hh:= mgerm (f:=fun x=> ∑ i∈range (r+1), (p.measure i:ℂ)*money (p.back r) 0 i 2 x) (g:=fun _=>1) (k:=v) (scale_pred p r)
   rw [mconst,msum (f:=fun i x=> (↑(p.measure i):ℂ)*money (p.back r) 0 i 2 x) _ fun i _=> contDiffAt_const.mul (monetized (p.back r) 0 i 2)] at hh; rw [← hh]; exact sum_congr rfl fun i _=> (mul_comm ..).trans (mscale _ (monetized (p.back r) 0 i 2)).symm
-- exact second-order coefficient effect even though Sale applies frame to all ranks
lemma proceeds (hr:2≤r) (hw:p.EvenK r): motion (money (p.back r) 0 0 2) 2= -(p.measure 2:ℂ) := by
   let f i:= motion (money (p.back r) 0 i 2) 2 * (p.measure i:ℂ); have he:= p.horizon r 2
   change ∑ i∈ range (r+1), f i = _ at he
   rw [← sum_subset (show range 3⊆range (r+1) from range_mono (by omega)),if_neg (by omega)] at he; swap
   · intro i hi hk; have hi : 2 < i:= by simp only [mem_range] at hk; omega
     unfold f; rw [triangular,if_neg hi.not_ge,zero_mul]
   have hf:f 1=0:= by unfold f; rw [hw _ (by omega) odd_one,Complex.ofReal_zero,mul_zero]
   rw [sum_range_succ,sum_range_succ,sum_range_one,hf,add_zero] at he; unfold f at he; rw [this_step,one_mul,p.starts,Complex.ofReal_one,mul_one] at he; exact eq_neg_of_add_eq_zero_left he

variable {u:Display X} {m:ℕ→ℤ}(h:Charge r m u)(J : T X ℂ 2 →ₗ[ℂ] ℂ)
abbrev SymbolPaid : Prop := ∀ i≤r,J (iteratedFDeriv ℝ 2 (u i) 0)= -(p.measure i:ℂ)
include h in
lemma ranking (hv : p.SymbolPaid r (u:=u) J)(i:ℕ) (_ : i≤r) : J (iteratedFDeriv ℝ 2 (born u (p.back r) 0 r i) 0)=if i=0 then (-1) else 0:= by
   rw [Ranking.price ζ 0 h, sum_congr rfl (g:=fun j=> motion (money (p.back r) 0 j 2) i * -(p.measure j:ℂ)) fun j hj=> by rw [hv j (mem_range_succ_iff.mp hj)]]; simp_rw [mul_neg,sum_neg_distrib, horizon]; split <;> simp
include h in
lemma paid_even (hv:p.SymbolPaid r (u:=u) J)(hp : Preserves.Weight u r 1) : p.EvenK r := by
   intro i hi he
   let f:= u i
   have ht : ∀ x:X, Assembly.jet f 2 x=0 := by
      intro x
      have hh:= (h i hi).smooth.contDiffAt (x:=0)
      let l:ℝ→L[ℝ] X:= (ContinuousLinearMap.id ℝ _).smulRight x
      have hl : motion (f ∘ l) 2=Assembly.jet f 2 x:= by rw [motion, Assembly.jet_continuous_right l (hh.of_le le_top), show l 1=x from one_smul ℝ x]
      have heq(v:X): f (-v)= -f v:= by unfold f; rw [hp i hi,he.neg_one_pow, one_mul,neg_one_mul]
      have hu : (fun u:ℝ=> (f ∘ l) (-u)) = fun u=>(-1:ℂ)*(f ∘ l) u:= by simp_rw [Function.comp_apply,map_neg,heq,neg_one_mul]
      have hc:ContDiffAt ℝ ω (f ∘ l) 0:= (l.map_zero.symm ▸ hh:ContDiffAt ℝ ω f (l 0)).comp _ l.contDiff.contDiffAt
      have hh:= Preserves.motneg hc 2; rw [hu,mscale _ hc,hl,neg_one_sq,one_mul,neg_one_mul] at hh; exact neg_eq_self.mp hh
   have hc : iteratedFDeriv ℝ 2 (u i) 0=0:= by refine Tensor.ext_diag _ _ (YM.Analysis.sym_Jet ((h i hi).smooth.contDiffAt.of_le le_top)) (fun _ _=>rfl) (funext fun x=>?_); change _=(0:ℂ); exact (smul_right_inj (show ( (Nat.factorial 2:ℝ)⁻¹)≠0 from by positivity)).mp ((ht x).trans (smul_zero _).symm)
   have hh:=hv i hi; rw [hc,map_zero] at hh; exact Complex.ofReal_eq_zero.mp (neg_eq_zero.mp hh.symm)
end Caliber
end YM.Comparison.RG02.Adjacent

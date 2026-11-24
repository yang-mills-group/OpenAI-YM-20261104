import YM.QuadraticLocal.Startup.Arbor
import YM.QuadraticLocal.Earn.Temp
import YM.QuadraticLocal.Germ.Annual

/-! # qlocal launch cost of all field-unmasked analytic insertions

Rows can have prefactors with **negative coupling exponents**. Allow all the nonempty
modes in the test suite, including `clear` rows which don't use a mask. Buy
(1 + 2/threshold)^s to switch to the actual off-mask full-group norm.
This is only in the analysis of *installing force* with a temporarily shrunk polydisk.
`ShiftRows` handles the corresponding entire polynomial (incl. the full actual vacuum).
The regular error will not be charged this startup cost! -/

set_option autoImplicit false
noncomputable section

namespace YM.QuadraticLocal.Spill

open Function Filter Finset Wilson Lattice RG Marker Ac Push Push.AbsoluteSums MeasureTheory
open Corrected QuadraticLocal.Earn Next.Scheduling
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge} {n:Side} {α:Type}
variable {V ι:Type}[DecidableEq V]{R:Census V}{D:Passport n V}
variable (X: ι→ Row D R G α) (B: BudgetPoint) (g:ℝ) (s:ℕ)
variable (t:α) (i:ι)
variable {w:V→ℝ}{a b f τ c k z η:ℝ}

open Row

def allOver (B:BudgetPoint) : ℝ := 1+2/B.threshold
lemma allOver_ge : 1≤ allOver B := le_add_of_nonneg_right (div_nonneg zero_le_two B.threshold_pos.le)

lemma nominal_price (A: Row D R G α) (hc:A.Budget) (hs:A.lamp.r≤ s) (U:Config G n) :
    ‖A.nominal g t U‖ ≤ allOver B ^ s * A.charge B g := by
  let j:= A.lamp.r
  let v:= |g^A.lamp.lag|
  let F:=A.atom
  let T:=allOver B
  have hT : 1 ≤ T:= allOver_ge B
  have hv:0 ≤ v:= abs_nonneg _
  have hx := A.sound.le
  have hy : 0≤ F.magnitude:= Invoice.p_bound _ _
  have ht := B.threshold_pos
  have hT': (2:ℝ)^j ≤ T^j * B.threshold^j := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ zero_le_two _ j
    rw [show T * B.threshold = B.threshold + 2 from (by unfold T allOver; field_simp; try ring)]
    exact le_add_of_nonneg_left ht.le
  let p:=Wages.price B F
  have hp₀ : F.magnitude * B.threshold^j ≤ p:= by
    unfold p
    rw [Wages.scan]
    let br:=(F.length:ℝ) + 1
    have he:1 ≤ br:= le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hg : 1≤ Wages.startup G j B.power B.order := Invoice.settledP ..
    exact le_trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (pow_nonneg ht.le _) hg) hy) (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (zero_le_one.trans hg) (pow_nonneg ht.le _)) hy) (one_le_pow₀ he)) -- multiplication rhs p unfolds Wages.startup macro
  have hz: 0 ≤ p:= (mul_nonneg hy (pow_nonneg ht.le _)).trans hp₀
  have hb₁ : F.magnitude * 2^j ≤ T^s * p:=calc
    _ ≤ F.magnitude * (T^j*B.threshold^j):=mul_le_mul_of_nonneg_left hT' hy
    _ = T^j * (F.magnitude * B.threshold^j):= mul_left_comm ..
    _ ≤ T^s * p:= mul_le_mul (pow_le_pow_right₀ hT hs) hp₀ (mul_nonneg hy (pow_nonneg ht.le _)) (pow_nonneg (zero_le_one.trans hT) _)
  have hb₂: v*p ≤ A.baseCost B g:= by
    refine le_mul_of_one_le_left (mul_nonneg hv hz) ?_
    exact one_le_pow₀ (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  rw [Row.nominal, Pi.smul_apply, norm_smul, Complex.norm_real]
  change ‖A.paint t‖ * |g^A.lamp.lag * F.unmasked U A.center| ≤ _
  rw [abs_mul]; calc
    _ ≤ A.salary * (v * (T^s * p)):= mul_le_mul (hc t) (mul_le_mul_of_nonneg_left ((A.atom.unmasked_bound ..).trans hb₁) hv) (mul_nonneg hv (abs_nonneg _)) hx
    _ = T^s * ((v*p) * A.salary) := by ring
    _ ≤ _:= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb₂ hx) (pow_nonneg (zero_le_one.trans hT) _)

set_option quotPrecheck false
local notation "Λ"=> rendered X B g
local notation "L" i:max=> (rendered X B g).ground i

open Canopy

def raw (t:α)(i:ι)(U:Config G n):Poly R:= Poly.send (X i).mode ((X i).nominal g t U)
abbrev Worn (i:ι) (U:Config G n): Prop:= (X i).clear ∨ Healthy B.threshold ((X i).ground B) U

def off (t:α)(i:ι)(U:Config G n):Poly R:= if Worn X B i U then 0 else raw X g t i U

def shifts : ShiftRows α ι G B D.origin R where
  place i:= ⟨(X i).ground B, ⟨_, (X i).starts _⟩⟩
  soap:= off X B g
  cost t i:= by
    let h:= (X i).legal B g t
    refine ⟨fun q U=> ?_, ?_, fun u v he hp=>?_, fun U p hp x hx=>?_⟩
    · unfold off raw Worn Healthy; rw [gauge_flags,h.symmetry]
    · by_cases he:(X i).clear
      · simp_rw [funext (fun U=> show off X B g t i U=0 from (by simp [off,Worn,he]))]; exact measurable_const
      simp_rw [funext (fun U=> show off X B g t i U= if Healthy B.threshold _ U then 0 else raw X g t i U from (by simp [off,Worn,he]; rfl))]
      exact Measurable.ite (healthy_closed _ _).measurableSet measurable_const ((Overlay.Bands.sends _).measurable.comp h.borel)
    · have hy:Healthy B.threshold ((X i).ground B) u = Healthy B.threshold ((X i).ground B) v:= by
        unfold Healthy; simp only [Finset.disjoint_iff_inter_eq_empty]; rw [hp]
      simp only [off,Worn,hy,raw,h.sites u v he]
    unfold off at hp; split at hp; contradiction; unfold raw at hp; rw [Poly.part_send] at hp; split at hp; subst p; exact (Λ).roots _ _ hx; exact (hp rfl).elim
  clean t i U h:= by
    unfold off at h; split at h; contradiction
    exact fun hh=> ‹¬ Worn X B i U› (Or.inr hh)
  skip t i U:=by unfold off raw; split; rfl; rw [Poly.part_send,if_neg (show R.quiet ≠ (X i).mode from Λ|>.live i|>.symm)]
  single t i U:=by
    unfold off; split; rw [mul_zero]
    next he=>
      ext p; unfold raw; change (Poly.prod _ _).part p=0
      rw [Poly.cart,if_neg (show ¬(Poly.merges (X i).mode (X i).mode p) from fun hx=> (X i).binder.live (Subtype.ext (disjoint_self.mp hx.1)))]

lemma raw_eq (U:Config G n) : raw X g t i U = (Λ).frame i t U+ (shifts X B g|>.soap t i U):= by
  change _= _ + off X B g t i U
  unfold off raw Lamps.frame Lamps.light
  by_cases ht: (X i).clear
  · rw [if_pos (show Worn X B i U from .inl ht), if_pos (show (Λ).clear i from ht), add_zero]; rfl
  by_cases h:Healthy B.threshold ((X i).ground B) U
  · rw [if_pos (show Worn X B i U from .inr h),if_neg (show ¬ (Λ).clear i from ht),add_zero, masked_eq _ _ _ _ (show Healthy B.threshold (L i) U from h)]; rfl
  rw [if_neg (show ¬ Worn X B i U from (by simp [Worn,h,ht])), if_neg (show ¬ (Λ).clear i from ht), masked_ne _ _ _ _ (show ¬ Healthy B.threshold (L i) U from h),Poly.send_zero,zero_add]

variable {j k₁ q:ℕ} {r ξ:ℝ} {η₀:V→ℕ}
variable (hv:Scene.Armada X w η₀ r c j k₁ q) (he:Invoice.Supports B z a g r ξ)
local notation "I"=> Invoice.price B z (j+q+1) k₁ a ξ G
local notation "H"=> ((allOver B)^(j+q+1))
local notation "Σ_"=> shifts X B g
include hv he
lemma rent : (Σ_).Budget w B.B a ( H *(( I )*c)):= by
  let v i:= (X i).charge B g
  let f i:= H * v i
  let g' i:= Poly.send (X i).mode (↑(f i):ℂ)
  have ht:0 ≤ H:= pow_nonneg (zero_le_one.trans (allOver_ge B)) _
  have hb (i:ι) : 0≤ f i:= mul_nonneg ht (mul_nonneg (mul_nonneg (by positivity) ((X i).real_quote B g).1 ) (X i).sound.le )
  have ho(i:ι)(t:α)(U:Config G n) : ‖(X i).nominal g t U‖ ≤ f i:= nominal_price B g _ t _ (hv.honor i) (Scene.Armada.degreeR _ hv.toMinistry (X i) (hv.purchases.usable i)|>.2.2) _
  refine ⟨g',fun i t U p=> ?_, fun x=>?_⟩
  · unfold g'; rw [Poly.part_send]
    change ‖(off _ _ _ _ _ _).part p‖ ≤ _ ∧ _
    unfold off raw; split
    next=> by_cases he:p=(X i).mode; rw [if_pos he]; exact ⟨by simpa using hb i,rfl⟩; simp [he]
    next=> rw [Poly.part_send]; by_cases he:p=(X i).mode
           · simp only [if_pos he]; exact ⟨ho i t U,rfl⟩
           simp [he]
  convert budget_scale ht ( Scene.Armada.hits _ _ _ hv B he x ) using 1
  ext i; unfold g'; dsimp only [shifts]; rw [Poly.solo,Complex.norm_real,Real.norm_of_nonneg (hb i)]
  split
  next yes=>
    unfold Invoice.income f v; ring
  next no=> rw [mul_zero]

lemma allowance (hq:1≤ η) : (Σ_).Budget (Stoop.radius w η) B.B a ( H *(( I )*(η⁻¹*c))) :=
  rent X B g (hv.stored hq) he
omit hv he

variable {Y:V→Type} [∀ i,AddCommGroup (Y i)][∀ i,Module ℝ (Y i)]
variable {Actors:∀ i,Set (Y i)}{K:∀ i,Submodule ℝ (Y i)}
variable {S:ι→ Row D R G (Affinity.Wallet Actors)}
open Affinity
local notation "ℜ"=> shifts S B g
lemma retains (h:Tableau K Actors S)(U:Config G n) : Stencil D.support Actors K ((ℜ).place i).val (fun t=>(ℜ).soap t i U):=by
  refine ⟨fun p=>?_⟩; change Addressable _ _ _ _ p.val (fun t=>(off S B g t i U).part p)
  unfold off raw; split
  next=> simp_rw [Poly.part_nil]; exact Addressable.gone
  next=>
    simp_rw [Poly.part_send]; split
    next h'=> subst p; exact ⟨(h.line B g).adv i U, fun _ _ v hv=> (S i).heard _ v hv⟩
    next=> exact Addressable.gone

end YM.QuadraticLocal.Spill

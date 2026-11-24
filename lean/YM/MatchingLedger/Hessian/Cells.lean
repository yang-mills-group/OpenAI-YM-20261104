import YM.Pert.Kinetic.Panel
import YM.MatchingLedger.Layout

/-!
# Size-lifted currency on ANY represented history's kinetic projection

Probe at the two-component true long waves. The inverse kinetic price is huge at these
frequencies; do *not* just throw a volume-independent background error into the tested Hessian.
Pay all supports. First build the native weighted projection dictionary. Proofs below work even
without translation symmetry. This is a rate test at actual period, *not* imposing test
compatibility between different periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Spring
open Function Filter Lattice Wilson RG Exterior Precision Work.F03 Pert Pert.Kinetic
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {n : Side}
abbrev Floor (n : Side) := Site n→ ℝ -- max norm
abbrev Block (n : Side) := Site n→ Site n → ℝ -- max; no accidental different norm

def beam (r : ℝ)(x y:Site n) := Real.exp (r * separation x y)
lemma beam_pos (r:ℝ)(x y:Site n) : 0<beam r x y:= Real.exp_pos _
lemma beam_one {r:ℝ}(hr:0≤r)(x y:Site n) : 1≤beam r x y:= Real.one_le_exp (mul_nonneg hr (Nat.cast_nonneg _))
lemma beam_comm (r:ℝ)(x y:Site n) : beam r x y=beam r y x:= by unfold beam; rw [separation_comm]
lemma beam_merge {r:ℝ} (hr:0≤r)(x y z:Site n) : beam r x z≤beam r x y * beam r y z:= by
  unfold beam; rw [← Real.exp_add,← mul_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast separation_triangle x y z) hr)

def paid (A : Block n) (r:ℝ) := ∑ i, ∑ j, ‖A i j‖ * beam r i j
lemma paid_nn (A : Block n) (r:ℝ): 0≤ paid A r:= Finset.sum_nonneg (fun _ _=> Finset.sum_nonneg fun _ _=> mul_nonneg (norm_nonneg _) (beam_pos ..).le)
lemma paid_scale (x:ℝ)(A : Block n)(r:ℝ) : paid (x • A) r=‖x‖ * paid A r:= by unfold paid; simp only [Pi.smul_apply, smul_eq_mul,norm_mul,Finset.mul_sum,mul_assoc]
lemma paid_add (A B: Block n)(r:ℝ) : paid (A+B) r ≤ paid A r + paid B r:= by
  unfold paid; simp_rw [← Finset.sum_add_distrib,← add_mul]; exact Finset.sum_le_sum fun i _=> Finset.sum_le_sum fun j _=> mul_le_mul_of_nonneg_right (norm_add_le ..) (beam_pos ..).le
lemma paid_many {ι:Type*}(f:ι→Block n)(s:Finset ι)(r:ℝ) : paid (∑ i∈s,f i) r ≤ ∑ i∈s,paid (f i) r:= by induction s using Finset.induction_on with | empty=> simp [paid] | insert a s h ih=> simp_rw [Finset.sum_insert h]; exact (paid_add _ _ r).trans (add_le_add_right ih (paid (f a) r)) -- arg orientation?

lemma paid_entry {A : Block n}{r : ℝ} (hr:0≤r)(x y:Site n): ‖A x y‖ ≤ paid A r:=
  ((le_mul_of_one_le_right (norm_nonneg _) (beam_one hr x y)).trans (Finset.single_le_sum (f:=fun i=> ‖A x i‖ * beam r x i) (fun _ _=> mul_nonneg (norm_nonneg _) (beam_pos ..).le) (Finset.mem_univ y))).trans (Finset.single_le_sum (f:=fun i=> ∑ j, ‖A i j‖*beam r i j) (fun _ _=> Finset.sum_nonneg fun _ _=> mul_nonneg (norm_nonneg _) (beam_pos ..).le) (Finset.mem_univ x))

section infinite
variable {ι : Type*} {A : ι → Block n} {z : ι→ℝ} {r : ℝ} (he : Summable z) (hr:0≤r) (hf : ∀ i, paid (A i) r ≤ z i)

include hr he hf
lemma paid_available : Summable (A) := by
  apply Summable.of_norm_bounded he
  intro i; have h : 0≤ z i:= (paid_nn ..).trans (hf i); exact (pi_norm_le_iff_of_nonneg h).mpr fun x => (pi_norm_le_iff_of_nonneg h).mpr fun y=> (paid_entry hr _ _).trans (hf i)
lemma paid_rows (x y : Site n) : Summable fun i=> ‖A i x y‖ := Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> (paid_entry (A:=A i) hr x y).trans (hf i)) he
lemma paid_rises (x y : Site n) : (∑' i, A i) x y=∑' i,A i x y:= by rw [tsum_apply (paid_available he hr hf),tsum_apply]; exact Pi.summable.mp (paid_available he hr hf) x -- lemma name
lemma paid_all : paid (∑' i,A i) r≤∑' i,z i:= by
  simp_rw [paid,paid_rises he hr hf]
  calc _ ≤ ∑ x, ∑ y, (∑' i, ‖A i x y‖) * beam r x y:= Finset.sum_le_sum fun x _=> Finset.sum_le_sum fun y _=> mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (paid_rows he hr hf x y)) (beam_pos ..).le
       _ = ∑' i, paid (A i) r:= by
          unfold paid; simp_rw [← tsum_mul_right]; let k(x y:Site n):= (paid_rows he hr hf x y).mul_right (beam r x y)
          have hx:= Summable.tsum_finsetSum (fun i (_:i∈Finset.univ)=> summable_sum (fun j (_:j∈Finset.univ)=> k i j)); rw [hx]; simp_rw [Summable.tsum_finsetSum (fun j (_:j∈Finset.univ)=> k _ j)] -- dependent `_`
       _ ≤ ∑' i,z i := (Summable.of_nonneg_of_le (fun i=> paid_nn _ _) hf he).tsum_le_tsum hf he
end infinite

def utter (A : Block n) (T : Block n) := ∑ i:Site n, ∑ j:Site n, A i j * T i j

def spur (u v:Floor n) : Block n := fun i j=>u i * v j
def pulse (A : Block n) (v w:Floor n) := utter A (spur v w)
lemma utter_comm (A T:Block n) : utter A T=utter T A:= by unfold utter; simp_rw [mul_comm (A _ _)]
lemma utter_scale (u : ℝ)(A T:Block n): utter (u • A) T=u*utter A T:= by unfold utter; simp only [Finset.mul_sum,Pi.smul_apply,smul_eq_mul,mul_assoc]
lemma utter_plus (A Z T:Block n): utter (A+Z) T=utter A T+utter Z T:= by simp only [utter,Pi.add_apply,add_mul,Finset.sum_add_distrib]
lemma utter_many {ι:Type*}(f:ι→Block n)(X:Finset ι)(T:Block n): utter (∑ i∈X,f i) T=∑ i∈X,utter (f i) T:= by induction X using Finset.induction_on with | empty=> simp [utter] | insert a s h ih=> rw [Finset.sum_insert h,Finset.sum_insert h,utter_plus,ih]
lemma utterCLM (T : Block n) : ∃ L: Block n→L[ℝ]ℝ, ∀ A, L A=utter A T:= by
  let L : Block n→ₗ[ℝ]ℝ := { toFun A := utter A T,
                               map_add' := fun x y=> utter_plus x y T,
                               map_smul' := fun u A=> utter_scale u A T }
  exact ⟨LinearMap.toContinuousLinearMap L,fun _=>rfl⟩
lemma utter_infinite {ι:Type*}{A : ι → Block n}(h : Summable A)(T : Block n) : utter (∑' i,A i) T=∑' i,utter (A i) T:= by obtain ⟨L,e⟩:= utterCLM T; simp_rw [←e]; rw [L.map_tsum h]

lemma pulse_sum_left (A:Block n)(x y z:Floor n) : pulse A (x+y) z=pulse A x z+pulse A y z:=by simp only [pulse,utter,spur,Pi.add_apply, add_mul,mul_add, Finset.sum_add_distrib]
lemma pulse_sum_right (A:Block n)(x y z:Floor n) : pulse A x (y+z)=pulse A x y+pulse A x z:=by simp only [pulse,utter,spur,Pi.add_apply,mul_add, Finset.sum_add_distrib]

def spot (x : Site n) : Floor n:= fun i=> if i=x then 1 else 0
lemma pulse_spots (A : Block n)(x y : Site n) : pulse A (spot x) (spot y)=A x y:= by simp [pulse,utter,spur,spot, mul_ite]
lemma surface_basis (a : Floor n): a=∑ i,a i • spot i:= by ext1 k; simp_rw [Finset.sum_apply, Pi.smul_apply, spot,smul_eq_mul,mul_ite,mul_one,mul_zero]; rw [Finset.sum_ite_eq]; simp

-- symmetrize without assuming the loop pricing is symmetric per label

def reversed (A : Block n) : Block n:= fun i j=> A j i
lemma paid_rev (A:Block n) (r:ℝ): paid (reversed A) r= paid A r:= by unfold paid reversed; rw [Finset.sum_comm]; simp_rw [beam_comm]; -- risk simp loop

def angle (A : Block n) := (2:ℝ)⁻¹ • (A+reversed A)
lemma ticks (A:Block n) (i j: Site n) : angle A i j=(A i j + A j i)/2:= by unfold angle; simp [reversed,div_eq_mul_inv,mul_comm]
lemma angle_sym (A:Block n) (i j:Site n): angle A i j=angle A j i:= by rw [ticks,ticks,add_comm]
lemma paid_angle (A:Block n)(r:ℝ): paid (angle A) r≤ paid A r:= by
  unfold angle; rw [paid_scale, Real.norm_of_nonneg (inv_nonneg.mpr zero_le_two)]
  have h:= paid_add A (reversed A) r; rw [paid_rev] at h; apply le_trans (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr zero_le_two)); linarith
lemma utter_reversed (A T:Block n) : utter (reversed A) (reversed T)=utter A T:= by unfold reversed utter; exact Finset.sum_comm
lemma pulse_angle (A:Block n)(v:Floor n): pulse (angle A) v v=pulse A v v:=by
  unfold pulse angle; rw [utter_scale,utter_plus]; nth_rw 2 [← show reversed (spur v v)=spur v v from by funext i j; exact mul_comm _ _]; rw [utter_reversed]; ring
lemma matrix_card {A B:Block n} (hB:∀ i j,B i j=B j i) (h:∀ u:Floor n, pulse A u u=pulse B u u): angle A=B:= by
  funext i j; have he:= h (spot i+spot j); simp only [pulse_sum_left,pulse_sum_right] at he; rw [h _,h _] at he 
  simp_rw [pulse_spots] at he; rw [hB j i] at he; rw [ticks]; linarith only [he]

end YM.MatchingLedger.Spring

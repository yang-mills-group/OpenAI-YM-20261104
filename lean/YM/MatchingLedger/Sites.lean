import YM.MatchingLedger.Coercive
/-!
# Regional action bound (not clipped)

Patch collar; no seam accounting omitted. Positive terms are from the actual
Wilson energy and kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Action
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision
open PatchArea Push.SectorMeasure
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {c f : Side} (S : StepData c f) {G : Gauge}

def total (R : Support c) (a : Site c→ℝ) := ∑ i∈R,a i
lemma total_add (R : Support c)(f g : Site c → ℝ) :
    total R (fun x=> f x+g x) = total R f + total R g := Finset.sum_add_distrib
lemma total_scale (R : Support c)(a : ℝ)(f : Site c → ℝ) : total R (fun x=> a * f x)= a * total R f := (Finset.mul_sum ..).symm
lemma total_split (R : Support c)(f : Site c → ℝ) : total Finset.univ f=total R f + total Rᶜ f := (Finset.sum_add_sum_compl ..).symm
lemma total_const (R : Support c)(a : ℝ) : total R (fun _=>a) = R.card * a := by simp [total]
lemma total_nn {R : Support c} {a : Site c → ℝ} (ha : ∀ i, 0 ≤ a i) : 0 ≤ total R a := Finset.sum_nonneg (fun i _=>ha i)
lemma total_mono {f : Site c → ℝ}(hf : ∀ i, 0 ≤ f i) {R Q : Support c} (he : R⊆Q) : total R f ≤ total Q f :=
  Finset.sum_le_sum_of_subset_of_nonneg he (fun i _ _=> hf i)

-- Use footprint := patch collar; leaves beacons outside in antenna.
def belt (P : Patch) := radius P + 2

def rent (G : Gauge)(P : Patch)(K : KernelChoices) := coefficient G P K * park (radius P)
def upperFace (P : Patch) : ℝ := faceRent P * 16 * park 2
lemma rent_nn (G : Gauge)(P : Patch)(K : KernelChoices) : 0 ≤ rent G P K := mul_nonneg (coefficient_nn ..) (park_nn _)
lemma upperFace_nn (P : Patch) : 0≤upperFace P:= by unfold upperFace; have h:=park_nn 2; positivity

variable {S}
variable (R : Support c) {U : Config G f} (F : Forest S.ratio) (hF : SliceSet S F U) (hs : InRange S)
    {t : S.Choices} (ht : Alive S U t) (V : Config G c)
local notation "p" => S.patch
local notation "κ" => S.kernel
local notation "Y" => S.prediction U t

include hF hs ht
lemma pale : total R (links S U) ≤ (linkRent p * 4 : ℝ)*
      (rent G p κ * total (halo (radius p) R) (face S U) + total R (thread Y V) + total R (outside V)) := by
  let B(z : Site c) : ℝ := coefficient G p κ * total (halo (radius p) {z}) (face S U)
  have hp(z : Site c) : links S U z ≤ (linkRent p * 4 : ℝ)*(B z+thread Y V z + outside V z):= by
    apply le_trans (Finset.sum_le_sum (s:=located (region S) {z}) (f:=fun i=>G.chord (U i)^2)
      (by exact fun i hi => (show _ ≤ 4*(B z + thread Y V z + outside V z) from
        Finset.mem_singleton.mp (loc.mp hi) ▸ lowerOne F hF hs ht i V))) ?_
    rw [Finset.sum_const, nsmul_eq_mul, region_size S _ Axis, Finset.card_singleton,Nat.mul_one,← mul_assoc]; rfl
  have hv : total R B ≤ rent G p κ * total (halo (radius p) R) (face S U) := by
    unfold B rent; rw [total_scale, mul_assoc]; exact mul_le_mul_of_nonneg_left (point_pay _ _ _ (face_nn S U)) (coefficient_nn ..)
  have he:= Finset.sum_le_sum (s:=R) (by exact fun i _=>hp i); unfold total at *
  simp_rw [← Finset.mul_sum, Finset.sum_add_distrib] at he
  exact he.trans (mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add_left hv _) _) (by positivity))

lemma vivid : total R (thread Y V) ≤ 16*
      (rent G p κ * total (halo (radius p) R) (face S U) + total R (links S U) + total R (outside V)) := by
  let B(z : Site c) : ℝ := coefficient G p κ * total (halo (radius p) {z}) (face S U)
  have hp(z : Site c) : thread Y V z ≤ 16*(B z+links S U z + outside V z):= by
    have he := Finset.sum_le_sum (s:=Finset.univ) (f:=fun i:Axis=>(wire Y V (z,i))^2)
      (by exact fun i _ => upperOne F hF hs ht (z,i) V)
    change _ ≤ ∑ i:Axis,4*(B z+links S U z+ outside V z) at he
    exact he.trans_eq (by rw [Finset.sum_const,Finset.card_univ, nsmul_eq_mul]; simp; ring)
  have hv : total R B ≤ rent G p κ * total (halo (radius p) R) (face S U) := by
    unfold B rent; rw [total_scale, mul_assoc]; exact mul_le_mul_of_nonneg_left (point_pay _ _ _ (face_nn S U)) (coefficient_nn ..)
  have he:= Finset.sum_le_sum (s:=R) (by exact fun i _=>hp i); unfold total at *
  simp_rw [← Finset.mul_sum, Finset.sum_add_distrib] at he
  apply he.trans; exact mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add_left hv _) _) (by positivity)

-- constants after the block factor; defined positively without maximizing over sectors.
def lowerCost (G : Gauge) (P : Patch) (K : KernelChoices) :=
  1 + (linkRent P * 4:ℝ)*(rent G P K*2+2/K.penalty + 1)
def upperCost (G : Gauge) (P : Patch) (K : KernelChoices) :=
  1+upperFace P /2 + (K.penalty/2)*16*(rent G P K * upperFace P+1)
omit S hF hs ht in
lemma lower_pos (G : Gauge)(P : Patch)(K : KernelChoices) : 1 ≤ lowerCost G P K:= by unfold lowerCost; apply le_add_of_nonneg_right; positivity [K.penalty_pos,rent_nn G P K]
omit S hF hs ht in
lemma upper_pos (G : Gauge)(P : Patch)(K : KernelChoices) : 1 ≤ upperCost G P K:= by unfold upperCost; apply le_trans (le_add_of_nonneg_right ?_) (le_add_of_nonneg_right ?_) <;> positivity [upperFace_nn P,K.penalty_pos,rent_nn G P K]

lemma lower : (lowerCost G p κ)⁻¹ * total R (links S U) - total R (outside V) ≤
    total (halo (belt p) R) (bill S U V t) := by
  let H:=halo (belt p) R; let J:=halo (radius p) R
  let f:=total H (face S U); let u:=total H (thread Y V); let b:=total H (bill S U V t)
  let o:=total R (outside V)
  let X:=lowerCost G p κ; let t':=(κ).penalty; let Y':= rent G p κ
  let L : ℝ:= linkRent p*4
  have hx : b= (1/2:ℝ)*f + t'/2*u := (total_add H ..).trans (congr_arg₂ _ (total_scale H ..) (total_scale H ..))
  have hg : 0 ≤ f := total_nn (face_nn _ _); have hu : 0 ≤ u := total_nn (thread_nn Y V)
  have hk : 0 < t' := (κ).penalty_pos; have he : 0 ≤ Y' := rent_nn ..; have hp : 0 ≤ L := by unfold L; positivity
  have ho : 0 ≤ o := total_nn (outside_nn _); have hb : 0 ≤ b := total_nn (bill_nn S U V t)
  have hX : 0<X:= zero_lt_one.trans_le (lower_pos G p κ)
  apply (sub_le_iff_le_add).2
  change X⁻¹ * total R (links S U) ≤ b + o; apply (inv_mul_le_iff₀ hX).2
  have hm : total J (face S U) ≤ f := total_mono (face_nn S U) (Lattice.Corona.halo_mono (by unfold belt; omega) (fun i hi=>hi))
  have hq : total R (thread Y V) ≤ u := total_mono (thread_nn Y V) (halo_subset _ _)
  have he' : f ≤ 2*b := by rw [hx]; nlinarith only [mul_nonneg hu hk.le]
  have he₀ : 0 ≤ 2/t':= by positivity
  have hh : u ≤ (2/t') * b:= by rw [hx]; field_simp; linarith only [hg]
  refine (pale R F hF hs ht V).trans (le_trans (mul_le_mul_of_nonneg_left (add_le_add_left
    (add_le_add (mul_le_mul_of_nonneg_left (hm.trans he') he) (hq.trans hh)) o) hp) ?_)
  change L*(Y' * (2*b)+ (2/t') * b + o) ≤ (1+L*(Y'*2+2/t'+1))*(b+o)
  nlinarith only [hb,ho,mul_nonneg hp hb,mul_nonneg hp (mul_nonneg he ho),mul_nonneg hp (mul_nonneg he₀ ho)]

lemma upper : total R (bill S U V t) ≤ upperCost G p κ *
      (total (halo (belt p) R) (links S U) + total R (outside V)) := by
  let X:=total (halo (belt p) R) (links S U); let v:=total R (outside V)
  let u:=upperFace p; let y:=rent G p κ; let k:=(κ).penalty
  have hp: 0 ≤u:= upperFace_nn p; have he : 0≤y := rent_nn ..; have hk:0≤k:= (κ).penalty_pos.le
  have hv:0≤v := total_nn (outside_nn _); have hX : 0≤X := total_nn (links_nn _ U)
  have hh : total R (links S U) ≤ X := total_mono (links_nn S U) (halo_subset _ _)
  have hE : total (halo (radius p) R) (face S U) ≤ u*X:=
    (lightFace S U _).trans (mul_le_mul_of_nonneg_left (total_mono (links_nn S U) (advance R (radius p) 2)) hp)
  have hL : total R (face S U) ≤ u*X:=(total_mono (face_nn S U) (halo_subset (radius p) R)).trans hE
  have hy := (vivid R F hF hs ht V).trans (mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left hE he) hh) v) (by norm_num : (0:ℝ)≤16))
  have hi : total R (bill S U V t) ≤ (1/2)*(u*X) + k/2*(16*(y*(u*X)+X+v)):= by
    unfold bill; rw [total_add, total_scale,total_scale]; gcongr
  apply hi.trans; change (1/2)*(u*X) + k/2*(16*(y*(u*X)+X+v))≤(1+u/2+(k/2)*16*(y*u+1))*(X+v)
  nlinarith only [hv,hX,mul_nonneg hp hv,mul_nonneg hk (mul_nonneg he (mul_nonneg hp hv))]

end YM.MatchingLedger.Action

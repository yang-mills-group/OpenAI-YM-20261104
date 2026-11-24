import YM.RG06.Wilson.FrameRate
/-!
# Peeling the explicit formal t^-l prefactors

Ordinary coefficients only, take strict horizons via pop; no guess about the
actual RG threshold or canonicalization. Identifies the free input polynomial
(the minimum-degree part of the Pose, curls) and all interactions. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06
open GSeries Function Lattice RG
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius


namespace GSeries
variable {R : Type*} [Semiring R]

/-- Shift right by the number of announced slots (divide by that monomial
when it does divide). -/
def voice (l : ℕ) (P : PowerSeries R) := PowerSeries.mk (fun k=>PowerSeries.coeff (k+l) P)
@[simp] theorem coeff_voice (l k : ℕ) (P : PowerSeries R) :
    PowerSeries.coeff k (voice l P)=PowerSeries.coeff (k+l) P := PowerSeries.coeff_mk ..
@[simp] theorem voice_right (l : ℕ) (P : PowerSeries R): voice l (P * PowerSeries.X ^ l) = P :=
  PowerSeries.ext fun k=>by rw [coeff_voice,PowerSeries.coeff_mul_X_pow]

variable {S : Type*} [CommSemiring S]
theorem paid {l : ℕ} {P : PowerSeries S} (h : PowerSeries.X^l∣P) : voice l P * PowerSeries.X^l=P := by
  obtain ⟨V,hV⟩:=h; rw [hV, mul_comm (_^l),voice_right]

section Core
open MvPolynomial
variable {V I : Type*}
-- Expand a polynomial on legs when compiling. Keep general coefficient ring and
-- base map for reuse. -/
lemma coat_support (P : MvPolynomial I ℂ) (f : ℂ→+*PowerSeries S) (g : I → PowerSeries S) :
    eval₂Hom f g P =
      ∑ b ∈ P.support, f (coeff b P) * b.prod (fun i k=> g i ^ k) := by
  have he (b) (c:ℂ) : eval₂Hom f g (monomial b c)= f c * b.prod (fun i k=>g i^k) := by
    rw [monomial_eq, _root_.map_mul,eval₂Hom_C]; unfold Finsupp.prod; simp_rw [map_prod,map_pow,eval₂Hom_X']
  conv_lhs=> rw [← P.support_sum_monomial_coeff,_root_.map_sum]
  simp_rw [he]

lemma divide_at (P : MvPolynomial I ℂ) (f : ℂ→+*PowerSeries S) (g : I → PowerSeries S) (l : ℕ)
    (h : ∀ b∈P.support,l ≤ b.sum (fun _ j => j))
    (Q : ∀ i,PowerSeries.X ∣ g i) :
    PowerSeries.X ^ l ∣ eval₂Hom f g P := by
  rw [coat_support]; refine Finset.dvd_sum ?_; intro b hb; apply dvd_mul_of_dvd_right _ _
  apply Dvd.dvd.trans (pow_dvd_pow _ (h b hb))
  unfold Finsupp.prod Finsupp.sum
  simp only [] -- dsimp
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_dvd_prod_of_dvd _ _ (fun i _hi => pow_dvd_pow_of_dvd (Q i) _)

lemma monomial_peel (b : I →₀ ℕ) (g : I → PowerSeries S) (P : I → PowerSeries S)
    (hg : ∀ i ∈ b.support, g i=P i * PowerSeries.X) :
    b.prod (fun i k=>g i^k) = (b.prod fun i k=>P i ^ k) * PowerSeries.X ^ (b.sum (fun _ k=>k)) := by
  unfold Finsupp.prod Finsupp.sum
  dsimp; rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i hi=> by rw [hg _ hi, mul_pow]

def legCount (b : I →₀ ℕ) := b.sum fun _ k=>k

/-- Explicit slot division of a posed stencil. Used to identify its leading
coefficient as the exactly-minimum-slot polynomial evaluated on leading
(divided) legs, independently of higher curvature terms. -/
def peelPose (l : ℕ) (P : MvPolynomial I ℂ) (f : ℂ →+* PowerSeries S) (v : I → PowerSeries S) : PowerSeries S :=
  ∑ b∈P.support, (f (coeff b P) * b.prod (fun i k=> v i ^ k)) * PowerSeries.X ^ (legCount b - l)

lemma peelPose_shift (l : ℕ) (P : MvPolynomial I ℂ) (f : ℂ→+*PowerSeries S) (g : I→PowerSeries S)
    (v : I → PowerSeries S) (h : ∀ b∈P.support,l≤legCount b) (he : ∀ i, g i=v i * PowerSeries.X) :
    voice l (eval₂Hom f g P) = peelPose l P f v := by
  have hz : peelPose l P f v * PowerSeries.X ^ l = eval₂Hom f g P := by
    unfold peelPose
    rw [Finset.sum_mul,coat_support]; refine Finset.sum_congr rfl fun b hb=> ?_
    rw [monomial_peel b g v (fun i _=>he i), mul_assoc (f _ * _), ← pow_add,
      Nat.sub_add_cancel (h b hb)]
    exact mul_assoc ..
  rw [← hz,voice_right]

lemma constant_peel (l : ℕ) (P : MvPolynomial I ℂ) (f : ℂ→+*PowerSeries S) (v : I→PowerSeries S)
    (h : ∀ b∈P.support,l ≤ legCount b) :
    PowerSeries.constantCoeff (peelPose l P f v) =
    eval₂Hom (PowerSeries.constantCoeff.comp f) (fun i=>PowerSeries.constantCoeff (v i))
      (MvPolynomial.weightedHomogeneousComponent (fun _=>(1:ℕ)) l P) := by
  unfold peelPose
  have ei (b : I →₀ ℕ) : Finsupp.weight (fun _=>(1:ℕ)) b = legCount b := by simp [Finsupp.weight_apply,legCount]
  conv_rhs=> rw [coe_eval₂Hom,eval₂_eq]
  rw [MvPolynomial.support_weightedHomogeneousComponent, Finset.sum_filter,_root_.map_sum]; simp_rw [coeff_weightedHomogeneousComponent]
  apply Finset.sum_congr rfl; intro i hi
  rcases lt_or_eq_of_le (h i hi) with hv|e
  · simp [ei, ne_of_gt hv, _root_.map_mul, zero_pow (Nat.sub_pos_of_lt hv).ne']
  unfold Finsupp.prod
  simp [ei, ←e,_root_.map_mul,map_prod]
end Core
end GSeries

namespace WilsonCompiler
open Gauge Exterior

variable {G : Gauge} {V D : Type*} [AddCommGroup D] [One D]
variable (K : display G D V) (a : V→ℝ) (A : Links D G.Color)

lemma travel_flat (x : Four D) (w : Walk) : travel (roll A 0) x w=1 := by
  induction w generalizing x with
  | nil=>rfl
  | cons d w ih=> rw [travel,ih]; simp [Step.read,roll,G.mat_lieExp_zero]

lemma slotFlat (x : Four D) (s : Slot) : vertex x s (roll A 0)=0 := by simp [vertex, travel_flat]

theorem slot_null (G : Gauge) (x : Four D) (s : Slot) (i : G.ColorIndex) :
    PowerSeries.constantCoeff (slotSeq (basic G D) x s i) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  apply pigment_ext; intro a
  rw [← develop_coeff,← access_peel a, (slot_match (basic G D) _ (peeling G a) (basic_refines _) x s i).coeff, offer_zero]
  simp [slotFlat]

lemma sum_word (u : Links D G.Color) (x : Four D) (w : Walk) :
    Multiplicative.ofAdd (linkSum u x w) = travel (fun l=> Multiplicative.ofAdd (u l)) x w := by
  induction w generalizing x with
  | nil=>rfl
  | cons d w ih=>
    unfold linkSum travel; unfold Step.read; split <;>
      rw [← ih] <;> rfl

lemma slot_sum (u : Links D G.Color) (x : Four D) (s : Slot) :
    linkSum u x (Work.F02.slotWalk s) = linkSum u (stop x s.walk) (square s.plaq.val.1 s.plaq.val.2) := by
  apply Multiplicative.ofAdd.injective
  rw [sum_word, sum_word, Work.F02.slotWalk, travel_append, travel_append,stop_append,square_stop,travel_reverse]; simp only [mul_comm (travel _ x s.walk),mul_assoc,inv_mul_cancel, mul_one]

lemma travel_ray (x : Four D) (w : Walk) :
    HasDerivAt (fun r : ℝ => G.mat (travel (roll A r) x w)) (G.colorMat (linkSum A x w)) 0 := by
  induction w generalizing x with
  | nil=> rw [linkSum,map_zero]; exact hasDerivAt_const 0 (1:G.Mat)
  | cons d w ih=>
    let b : G.Color := if d.neg then -A (d.used x) else A (d.used x)
    let f (t : ℝ) := G.mat (d.read (roll A t) x)
    have he : HasDerivAt f (G.colorMat b) 0 := by
      have hw t : f t = G.mat (G.lieExp (t • b)) := by
        unfold f b Step.read roll
        split
        · rw [smul_neg, YM.Work.F03.exp_neg_color]
        rfl
      simp_rw [funext hw,G.mat_lieExp,map_smul]
      simpa using! hasDerivAt_exp_smul_const (G.colorMat b) (0:ℝ)
    simp_rw [travel,G.mat_mul]
    exact (he.mul (ih (x+d.vec))).congr_deriv (by change G.colorMat b * (fun _=>_) 0 + _ * _= _; unfold f; simp [Step.read,roll,travel_flat,G.mat_lieExp_zero,b,linkSum])

-- explicit scalar polynomial expression of the shifted leading curl on native single links
private def pureColor (k : G.ColorIndex) (l : DLink D) : Pigment (LinkVar G D) := MvPolynomial.X (l,k)

def solo (x : Four D) (s : Slot) (k : G.ColorIndex) : Pigment (LinkVar G D) :=
  linkSum (pureColor k) (stop x s.walk) (square s.plaq.val.1 s.plaq.val.2)

lemma solo_eval (x : Four D) (s : Slot) (k : G.ColorIndex) :
    tone (access G A) (solo x s k)= (linkSum A (stop x s.walk) (square s.plaq.val.1 s.plaq.val.2) k:ℂ) := by
  have he (w : Walk) (x : Four D) : tone (access G A) (linkSum (pureColor k) x w)=
      (linkSum A x w k:ℂ) := by
    induction w generalizing x with
    | nil=> simp [linkSum]
    | cons d w ih=>
      rw [linkSum,linkSum,map_add,ih]; split <;> simp [access,pureColor]
  exact he _ _

lemma slot_solo (A : Links D G.Color) (x : Four D) (s : Slot) (k : G.ColorIndex) :
    offer 0 1 (fun t=> (vertex x s (roll A t) k : ℂ)) =
      tone (access G A) (solo x s k) := by
  let W := Work.F02.slotWalk s
  let Y (t : ℝ) := G.mat (travel (roll A t) x W)
  let L := (paint k).toContinuousLinearMap
  change offer 0 1 (L ∘ Y) = _
  have he : HasDerivAt Y (G.colorMat (linkSum A x W)) 0 := travel_ray A x W
  simp only [offer,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,iteratedDeriv_one, solo_eval]
  rw [(L.hasFDerivAt.comp_hasDerivAt 0 he).deriv,slot_sum]
  change Complex.ofReal (G.projectColor ((1/2:ℝ) • (G.colorMat _ - star (G.colorMat _))) k)=_
  rw [G.colorMat_skew, sub_neg_eq_add, ← two_smul ℝ, smul_smul, div_mul_cancel₀ _ (two_ne_zero' ℝ), one_smul, G.project_colorMat]

theorem slot_head (G : Gauge) (x : Four D) (s : Slot) (k : G.ColorIndex) :
    PowerSeries.constantCoeff (voice 1 (slotSeq (basic G D) x s k))=solo x s k := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_voice]; apply pigment_ext; intro a
  rw [← develop_coeff,← access_peel a,(slot_match (basic G D) _ (peeling G a) (basic_refines _) x s k).coeff]
  exact slot_solo (peeling G a) ..

open MvPolynomial

theorem slot_division (G : Gauge) (x : Four D) (s : Slot) (i : G.ColorIndex) :
    PowerSeries.X ∣ slotSeq (basic G D) x s i := by
  rw [PowerSeries.X_dvd_iff, slot_null]

theorem skinned {m} (p : Bid.Pose G m) (b : ℕ) (hb : Bid.lows p b) (B : Fin m → Slot) (x : Four D) :
    PowerSeries.X ^ b ∣ frameFilm p B x (basic G D) := divide_at p _ _ b hb (fun i=> slot_division G x (B i.1) i.2)

/-- Weight l projection in ordinary **leg number**, not engineering order. -/
def frontPose {m : ℕ} (l : ℕ) (p : Bid.Pose G m) : Bid.Pose G m := weightedHomogeneousComponent (fun _=>(1:ℕ)) l p

def shiftedLead {m : ℕ} (p : Bid.Pose G m) (x : Four D) (l : ℕ) (B : Fin m → Slot) : Pigment (LinkVar G D) :=
  eval₂Hom MvPolynomial.C (fun i=> solo x (B i.1) i.2) (frontPose l p)

theorem free_leading {m : ℕ} (p : Bid.Pose G m) (l : ℕ) (hl : Bid.lows p l) (B : Fin m→ Slot) (x : Four D) :
    PowerSeries.constantCoeff (voice l (frameFilm p B x (basic G D))) = shiftedLead p x l B := by
  let f : ℂ →+* PowerSeries (Pigment (LinkVar G D)) := PowerSeries.C.comp MvPolynomial.C
  let k : Fin m × G.ColorIndex → PowerSeries (Pigment (LinkVar G D)) := fun i=>slotSeq (basic G D) x (B i.1) i.2
  let q i := voice 1 (k i)
  have he (i : Fin m × G.ColorIndex) : k i = q i*PowerSeries.X := by
    simpa only [pow_one] using (paid (l:=1) (P:=k i) (by rw [pow_one]; exact slot_division G _ _ _)).symm
  change PowerSeries.constantCoeff (voice l (eval₂Hom f k p))=_
  rw [peelPose_shift l p f k q hl he, constant_peel l p f _ hl]; unfold shiftedLead frontPose
  have ht : PowerSeries.constantCoeff.comp f=MvPolynomial.C := RingHom.ext (fun i=> PowerSeries.constantCoeff_C _)
  have hk : (fun i=>PowerSeries.constantCoeff (q i))=(fun i : Fin m × G.ColorIndex => solo x (B i.1) i.2) := funext fun i=> slot_head G ..
  rw [ht,hk]

section
open Source Wilson Labels
variable {d : ℕ} {F : Frame G d}
theorem coverQuot (C : Family G) (d : ℕ) (i : (C.labels.level d).Index) (h : Bid.pop (C.localSection d)) :
    PowerSeries.X ^ ((C.labels.level d).grades i).2 ∣ markTop C d (Pi.single i 1) := by
  obtain ⟨m,B,-,p,e,l⟩ := h i
  unfold markTop
  rw [formula_cover_eq _ p B (fun U=>congrFun e U)]; exact skinned _ _ l B _

theorem orbitQuot (C : Family G) (d : ℕ) (i : (C.labels.level d).Index) (h : Bid.pop (C.localSection d)) {n : Side} (x : Site n) :
    PowerSeries.X ^ ((C.labels.level d).grades i).2 ∣ markSite C d (Pi.single i 1) x := by
  obtain ⟨m,B,-,p,e,l⟩ := h i
  unfold markSite
  rw [formula_site_eq _ p B (fun U=>congrFun e U) x]; exact skinned _ _ l B _
end
end WilsonCompiler
end YM.RG06

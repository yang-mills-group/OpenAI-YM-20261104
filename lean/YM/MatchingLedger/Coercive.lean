import YM.MatchingLedger.Layout
import YM.Work.E02
import YM.Push.SECTOR_MEASURE.Cells

/-!
# Local, two-sided action cost on the *forest slice* for a conditioned bare step

Keep chords of the original predicted links, even on arbitrarily unhealthy fields.
Lower bound uses E02 (read its size and living-tag hypotheses). For the upper bound use it again,
now with the predicted links as an argument, reading an actual crossing of **each** bond.
This works although likelihoods depend on the fields (including fallback choices).
No compulsory-likelihood *lower* bound is used. But these coercive estimates are not yet
estimates for the law itself.

No estimate here for evaluating a perturbed log action **instead** of bare Wilson.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Action
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision
open PatchArea Push.SectorMeasure
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {c f : Side} (S : StepData c f) {G : Gauge}

/-- Start-site cost, in coarse units. -/
def links (U : Config G f) (x : Site c) : ℝ := ∑ i∈located (region S) {x}, G.chord (U i)^2

def face (U : Config G f) (x : Site c) : ℝ := ∑ i∈located (region S) {x}, (toll U i)^2

def thread (U V : Config G c) (x : Site c) : ℝ := ∑ a : Axis, (wire U V (x,a))^2

def outside (V : Config G c) (x : Site c) : ℝ := ∑ a : Axis, G.chord (V (x,a))^2

/-- Actual (one-channel) penalized score from the Wilson energy and full kernel penalty. -/
def bill (U : Config G f) (V : Config G c) (t : S.Choices) (x : Site c) :=
      (1/2 : ℝ) * face S U x + (S.kernel.penalty/2) * thread (S.prediction U t) V x

lemma links_nn (U : Config G f) (x : Site c) : 0 ≤ links S U x := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma face_nn (U : Config G f) (x : Site c) : 0 ≤ face S U x := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma thread_nn (U V : Config G c) (x : Site c) : 0 ≤ thread U V x := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma outside_nn (U : Config G c) (x : Site c) : 0 ≤ outside U x := Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma bill_nn (U : Config G f) (V : Config G c) (t : S.Choices) (x : Site c) : 0 ≤ bill S U V t x :=
  add_nonneg (mul_nonneg (by positivity) (face_nn ..))
    (mul_nonneg (by have := S.kernel.penalty_pos; positivity) (thread_nn ..))


variable {S}
/-- The E02 price to be purchased at each fixed ratio, patch and kernel. -/
def Budget (G : Gauge) (P : Patch) (K : KernelChoices) :=
    (Work.E02.answer G P.L P.J K).choose
lemma price_pos (G : Gauge) (P : Patch) (K : KernelChoices) : 0 < Budget G P K :=
    (Work.E02.answer G P.L P.J K).choose_spec.1

variable (S)
/-- Area costs imported as a unit. -/
structure InRange : Prop where
  size : 100*macroR S.patch ≤ f.val
  rim : 1 < c.val

variable {S}

private lemma patrol {U : Config G f} (F : Forest S.ratio) (hF : SliceSet S F U) (hs : InRange S)
    {t : S.Choices} (ht : Alive S U t) (e : Bond f) (V : Config G c) :
    Bid.Cops (S:=S) U V (S.prediction U t) e (Budget G S.patch S.kernel) :=
  (Work.E02.answer G S.patch.L S.patch.J S.kernel).choose_spec.2 c f S rfl rfl rfl hs.size hs.rim F U hF
    V e t (fun _ _=> listed_of_alive ht _)

private lemma travels_chord (U : Config G f) (a : ℝ) (w : Walk) (x : Site f)
    (h : ∀ i : Edge (Site f), i.1 ∈ visits x w → G.chord (U i) ≤ a) :
    G.chord (travel U x w) ≤ w.length * a := by
  induction w generalizing x with
  | nil => simp [travel]
  | cons i w ih =>
    have hx : G.chord (i.read U x) ≤ a := by
      rcases i with ⟨i,k|k⟩
      · exact h (x,i) (List.mem_cons_self)
      change G.chord (U (x-step i,i))⁻¹ ≤ _; rw [G.chord_inv]
      apply h; apply List.mem_cons_of_mem
      have h (z : Site f) (w : Walk) : z∈ visits z w := by cases w <;> simp [visits]
      change x-step i ∈ visits (x+ -(step i : Site f)) w
      rw [← sub_eq_add_neg]; apply h
    apply (G.chord_triangle _ _).trans
    refine (add_le_add hx (ih (x+i.vec) fun _ hh=> h _ (List.mem_cons_of_mem _ hh))).trans_eq ?_
    simp [add_mul, add_comm]

lemma near_face (S : StepData c f) (U : Config G f) (e : Cell f) :
    (toll U e)^2 ≤ 16 * ∑ x∈halo 2 {region S e}, links S U x := by
  let L := ∑ x∈halo 2 {region S e}, links S U x
  have hp : 0≤L := Finset.sum_nonneg fun _ _ => links_nn ..
  have he : toll U e ≤ 4*Real.sqrt L := by
    let p := square e.2.val.1 e.2.val.2
    refine (travels_chord U (Real.sqrt L) p e.1 ?_).trans_eq (by simp [p,square])
    intro i hx
    apply Real.le_sqrt_of_sq_le
    refine (Finset.single_le_sum (s:=located (region S) {region S i})
      (f:=fun i=>G.chord (U i)^2) (fun j _=>sq_nonneg _) (loc.mpr (Finset.mem_singleton_self _))).trans ?_
    exact Finset.single_le_sum (f:=links S U) (fun i _=>links_nn ..) (near_root.mpr (near_visit S e i.1 hx))
  exact (pow_le_pow_left₀ (G.chord_nonneg _) he 2).trans_eq (by rw [mul_pow,Real.sq_sqrt hp]; norm_num [L])

def faceRent (P : Patch) : ℕ := Fintype.card PlaqAxes * Fintype.card (Site P.L)
def linkRent (P : Patch) : ℕ := Fintype.card Axis * Fintype.card (Site P.L)
def park (n : ℕ) := ((↑(n+n+1):ℝ)^4)
lemma park_nn (n : ℕ) : 0 ≤ park n := by unfold park; positivity
lemma lightFace (S : StepData c f) (U : Config G f) (R : Support c) :
    ∑ x ∈ R, face S U x ≤ faceRent S.patch * 16 * park 2 * ∑ x∈halo 2 R, links S U x := by
  have hc x : face S U x ≤ faceRent S.patch * (16:ℝ) * ∑ i∈halo 2 {x}, links S U i := by
    unfold face; apply le_trans (Finset.sum_le_sum (s:=located (region S) {x})
      (fun i hi => (show toll U i^2 ≤ 16 * ∑ y∈halo 2 {x}, links S U y from
        Finset.mem_singleton.mp (loc.mp hi) ▸ near_face S U i))) (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, region_size S {x} PlaqAxes, Finset.card_singleton,Nat.mul_one, ←mul_assoc]; rfl
  have hh := point_pay R 2 (links S U) (links_nn S U)
  apply (Finset.sum_le_sum fun i _=> hc i).trans
  rw [← Finset.mul_sum, mul_assoc ((faceRent S.patch:ℝ)*(16:ℝ))]; exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- Cost of the macro plaquette input to Work.E02, uniform including seams. -/
lemma cover (S : StepData c f) (hs : InRange S) (U : Config G f) (x : Site c) :
    port S x U ^2 ≤ (faceRent S.patch * park (PatchArea.radius S.patch)) * ∑ i ∈ halo (PatchArea.radius S.patch) {x}, face S U i := by
  have hm := hs.size
  have he : 2 * macroR S.patch < f.val := by have h : 0<f.val := f.pos; omega
  let a:= halo (PatchArea.radius S.patch) {x}; let T:= located (region (α:=PlaqAxes) S) a
  have hh : port S x U ≤ ∑ i∈T,toll U i:=by
    rw [Work.E01.port_charge, ← Finset.sum_subset (Finset.subset_univ T)]
    · apply Finset.sum_le_sum; intro i _; exact mul_le_of_le_one_left
        (G.chord_nonneg _) (by exact_mod_cast Work.E01.mcharge_le_one S he x i)
    intro i _ hi; rw [show Bid.mcharge S x i=0 from Nat.eq_zero_of_not_pos fun h=> hi
        (loc.mpr (near_root.mpr ((Work.E01.mcharge_maps S x i h).trans (radius_jets S.patch))))]; simp
  have hp : T.card ≤ faceRent S.patch * (((PatchArea.radius S.patch))+((PatchArea.radius S.patch))+1)^4 := by
    unfold T; rw [region_size]; apply Nat.mul_le_mul_left; simpa only [Finset.card_singleton,one_mul] using Lattice.Corona.halo_size {x} (PatchArea.radius S.patch)
  calc
    _ ≤ (∑ i∈T,toll U i)^2 := pow_le_pow_left₀ (Axial.faces_nonneg ..) hh _
    _ ≤ T.card * ∑ i∈T,toll U i^2 := by simpa using Finset.sum_mul_sq_le_sq_mul_sq T (fun _=>(1:ℝ)) (toll U)
    _ ≤ _ := by
      unfold face park
      rw [total_at (region S) (fun i=>toll U i^2)]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (Finset.sum_nonneg fun i _=>sq_nonneg _)

def coefficient (G : Gauge) (P : Patch) (K : KernelChoices) :=
  (Budget G P K)^2 * (faceRent P : ℝ)* park (radius P)

lemma coefficient_nn (G : Gauge) (P : Patch) (K : KernelChoices) : 0≤ coefficient G P K := by
  unfold coefficient; positivity [park_nn (radius P)]

private lemma chord_sq3 (x y z : ℝ): (x+y+z)^2 ≤ 4*(x^2+y^2+z^2) := by
  nlinarith only [sq_nonneg (x-y),sq_nonneg (z-y),sq_nonneg (x-z),sq_nonneg x,sq_nonneg y,sq_nonneg z]

lemma lowerOne {U : Config G f} (F : Forest S.ratio) (hF : SliceSet S F U) (hs : InRange S)
    {t : S.Choices} (ht : Alive S U t) (e : Bond f) (V : Config G c) :
    let Q := S.prediction U t; let x:=region S e
    G.chord (U e)^2 ≤ 4*(coefficient G S.patch S.kernel * (∑ i∈halo (PatchArea.radius S.patch) {x}, face S U i)+
                           thread Q V x + outside V x) := by
  intro Q x
  let H:= Budget G S.patch S.kernel; let a:=port S x U
  let Y:=wire Q V (x,e.2); let v:=G.chord (V (x,e.2)); let R := replica S.ratio V e
  have hh : G.chord (U e) ≤ H*a+Y+v:= by
    apply (show G.chord (U e) ≤ G.chord (U e* R⁻¹)+ G.chord R by simpa only [inv_mul_cancel_right] using! G.chord_triangle (U e* R⁻¹) R).trans
    apply add_le_add
    · apply (patrol F hF hs ht e V).trans; unfold Y; split; rw [add_zero]; exact le_add_of_nonneg_right (G.chord_nonneg _); rfl
    unfold R replica; split; rw [G.chord_one]; exact G.chord_nonneg _; rfl
  apply (pow_le_pow_left₀ (G.chord_nonneg _) hh 2).trans ((chord_sq3 _ _ _).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by norm_num); apply add_le_add
  · apply add_le_add; rw [mul_pow]; apply le_trans (mul_le_mul_of_nonneg_left (cover S hs U x) (sq_nonneg H)) (le_of_eq ?_); unfold coefficient H; ring
    exact Finset.single_le_sum (f:=fun i:Axis=>(wire Q V (x,i))^2) (fun i _=>sq_nonneg _) (Finset.mem_univ _)
  exact Finset.single_le_sum (f:=fun i:Axis=>G.chord (V (x,i))^2) (fun i _=>sq_nonneg _) (Finset.mem_univ _)

lemma upperOne {U : Config G f} (F : Forest S.ratio) (hF : SliceSet S F U) (hs : InRange S)
    {t : S.Choices} (ht : Alive S U t) (e : Bond c) (V : Config G c) :
    let Q := S.prediction U t; let x:= e.1
    wire Q V e ^2 ≤ 4*(coefficient G S.patch S.kernel * (∑ i∈halo (PatchArea.radius S.patch) {x}, face S U i)+
                           links S U x + outside V x) := by
  intro Q x
  let H := Budget G S.patch S.kernel; let a := port S x U; let v := G.chord (V e)
  obtain ⟨j,hj,hp⟩:= reaching S x e.2
  let z:Bond f := (j,e.2); let w:= U z
  have hy : S.ratio.parent j≠ S.ratio.parent (j+step e.2) := by rw [hp,hj]; exact (hop_ne _ _ hs.rim).symm
  have hx: G.chord (w*(Q e)⁻¹) ≤ H*a := by
    have h:=patrol F hF hs ht z Q
    unfold Bid.Cops at h; dsimp only at h; unfold z at h; dsimp only at h; rw [if_neg hy,hj] at h
    have he : replica S.ratio Q (j,e.2)=Q e := by unfold replica; rw [if_neg (Ne.symm hy),hj]
    rw [he, show wire (S.prediction U t) Q (x,e.2)=0 from (by unfold wire Q; simp),add_zero] at h
    exact h
  have hw : wire Q V e ≤ H*a + G.chord w + v:= by
    have hh : G.chord (Q e)⁻¹ ≤ G.chord w + H*a := by
      refine (le_trans (le_of_eq (congr_arg _ (inv_mul_cancel_left w _).symm)) (le_trans (G.chord_triangle w⁻¹ (w*(Q e)⁻¹)) ?_)) -- check orientation
      rw [G.chord_inv w]; exact add_le_add_right hx _
    have h:=G.chord_triangle (V e) (Q e)⁻¹; unfold wire v; linarith only [hh,h]
  apply (pow_le_pow_left₀ (G.chord_nonneg _) hw 2).trans ((chord_sq3 _ _ _).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (by norm_num); apply add_le_add
  · apply add_le_add; rw [mul_pow]; apply le_trans (mul_le_mul_of_nonneg_left (cover S hs U x) (sq_nonneg H)) (le_of_eq ?_); unfold coefficient H; ring
    exact Finset.single_le_sum (s:=located (region S) {x}) (f:=fun i=>G.chord (U i)^2) (fun i _=>sq_nonneg _) (a:=z) (loc.mpr (Finset.mem_singleton.mpr hj))
  exact Finset.single_le_sum (f:=fun i:Axis=>G.chord (V (x,i))^2) (fun i _=>sq_nonneg _) (a:=e.2) (Finset.mem_univ _)

end YM.MatchingLedger.Action

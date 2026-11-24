import YM.Pert.Flow.Product
/-! Engineering power test on fixed tensor arrays with normalized residual estimates. Finite horizon, discrete times. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Pert.Flow
open Function Filter Topology Price Finset Layer
open scoped Topology Classical
variable {V I : Type*} [Fintype V] [Fintype I]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Words (E V I : Type*) := ℕ → V → (I→V) → E
abbrev Rounds (V I : Type*) := V × (I → V)

/-- A moving-label price that gets hit by the tensor error. -/
def bond (Z W : TimeArray V) (n : ℕ) (j:V) (h:I→V) (a : Rounds V I) : ℝ :=
   W n j a.1 * (∏ i:I, Z n (a.2 i) (h i))
def uponFields (Z W : TimeArray V) (value : Words E V I) (n : ℕ) (j:V) (h : I→V) : E :=
   ∑ a:Rounds V I, bond Z W n j h a • value n a.1 a.2
def coupon (e:V→ℝ) (n:ℕ) (j:V) (h : I → V) := (e j)^n * (∏ i, (e (h i))⁻¹^n)

lemma bond_identity (Z W:TimeArray V) (e:V→ℝ) (n:ℕ) j (h:I→V) (a:Rounds V I) :
   bond (normalizeCols Z e) (normalizeRows W e) n j h a = coupon e n j h*bond Z W n j h a := by
   dsimp only [normalizeCols,normalizeRows,bond,coupon]
   rw [Finset.prod_mul_distrib]; ring
/-- H inverse on input and H on output transform a moving reading back to fixed physical fields (the Wilson-coefficient comparison on the moving labels needs the opposite change). The net engineering price, not just a common output-horizon bound. -/
lemma row_identity (Z W : TimeArray V) (e) (z : Words E V I) n j h :
   uponFields (normalizeCols Z e) (normalizeRows W e) z n j h = coupon e n j h • uponFields Z W z n j h := by
     simp_rw [uponFields,bond_identity,mul_smul,Finset.smul_sum]

variable {e:V→ℝ} {S A T U : TimeArray V} (h : Orientations e S A T U)
include h
private lemma tame_fee (c:I→V) (j) : tame
    (fun n=> ∑ a:Rounds V I, |bond (normalizeCols S e) (normalizeRows A e) n j c a|) :=
    sum_tame fun a _=> tamer (tame_times (f:=fun n=>normalizeRows A e n j a.1) (rowPrices h _ _).2
       (product_tame (s:=Finset.univ) (a:=fun i n=>normalizeCols S e n (a.2 i) (c i)) (fun i _=>(rowPrices h ..).1)))
       (fun i=> le_of_eq (abs_abs ..))

lemma partial_keep (z:Words E V I) (n) {x:ℝ} (hx : ∀ j c, ‖z n j c‖ ≤ x) (j c) :
   ‖coupon e n j c • uponFields S A z n j c‖ ≤ (∑ a:Rounds V I, |bond (normalizeCols S e) (normalizeRows A e) n j c a|)*x := by
   rw [←row_identity]
   apply (norm_sum_le (Finset.univ) _).trans
   rw [Finset.sum_mul]
   exact sum_le_sum fun _ _=> (norm_smul_le ..).trans (by rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hx ..) (abs_nonneg _))

omit h in
lemma uniform_words (z : Words E V I) (u:ℕ→ℝ) {p:ℕ}
   (h:∀ j c, ∃ D≥(0:ℝ),∀ᶠ n in atTop, ‖z n j c‖ ≤ D*|u n|^p) :
   ∃ D≥(0:ℝ),∀ᶠ n in atTop,∀ j c, ‖z n j c‖ ≤ D*|u n|^p := by
   choose d hd hD using h
   let D:=∑ j:V, ∑ c:I→V, d j c
   have hc j : 0 ≤ ∑ c:I→V, d j c:= sum_nonneg fun c _=>hd _ _
   have ht j c : d j c ≤ D:= (single_le_sum (s:=Finset.univ) (fun c _=>hd j c) (mem_univ c)).trans
      (single_le_sum (fun j _=>hc j) (mem_univ j))
   exact ⟨D,sum_nonneg (fun j _=>hc j), eventually_all.mpr fun j=>eventually_all.mpr fun c=> (hD j c).mono fun n hn=>hn.trans (mul_le_mul_of_nonneg_right (ht ..) (by positivity))⟩

/-- Price lemma with a *family* of scheme remainder tests, each through some finite truncation. One needs finitely many extra orders (bounded below by order plus unspecified basis price); no infinite series taken. -/
theorem coupon_keep (R:ℕ→Words E V I) {B:ℝ} (hB:0 < B) {u:ℝ→ℝ} (hu:Signature B u) (j c)
   (hR : ∀ p:ℕ, ∀ j c, ∃ D≥(0:ℝ),∀ᶠ n in atTop, ‖R p n j c‖ ≤ D*|u n|^p) (q:ℕ) :
   ∃ p:ℕ, p≥q ∧ ∃ D≥(0:ℝ),∀ᶠ n:ℕ in atTop, ‖coupon e n j c • uponFields S A (R p) n j c‖ ≤ D*|u n|^q := by
   let f n := ∑ a:Rounds V I, |bond (normalizeCols S e) (normalizeRows A e) n j c a|
   obtain ⟨s,B0,hB0,hC⟩:=pricedUpon hu (tame_fee h c j) hB
   obtain ⟨D,hD,hr⟩:= uniform_words (R (s+q)) (fun n=>u n) (hR (s+q))
   refine ⟨s+q,Nat.le_add_left ..,B0*D,mul_nonneg hB0 hD, ?_⟩
   filter_upwards [hC,hr] with n hC hr
   refine (partial_keep h _ n hr j c).trans ?_
   calc
       _ = (|u n|^s * |f n| * D) * |u n|^q := by
           change f n * (D*|u n|^(s+q)) = _
           have hf : f n ≥ 0 := sum_nonneg fun i _=> abs_nonneg _
           rw [pow_add,abs_of_nonneg hf];ring
       _ ≤ (B0*D)*|u n|^q := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hD) (by positivity)

end YM.Pert.Flow

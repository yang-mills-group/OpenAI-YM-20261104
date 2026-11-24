import YM.MatchingLedger.Draw
import YM.MatchingLedger.Pressure
import YM.Gauge.Size

/-!
# Local exponential (pressure) bound on the actual forest-slice law

Use erasure argument for one step *from Wilson*, with the physical kernel, conditional on the
output field `V`. The gauge of that field matters in evaluation of `outside` and of the estimate.
- Full fine field and every tag and all fallback choices.
- Full normalized denominator, no estimate using a torus-volume lower bound. Log mgf currency:
  births weighted costs with a factor `exp C`, don't use these as cost `C` without continuation
  (moments/tails).
- The boundary charge is absorbed, not supplied by specifying favorable boundary values.
- Post-block, before cutoff threshold choice. Works for all large enough periods (energy/gap
  input size condition), not using the number of blocks or translation invariance to estimate.
- Explicit for inverse bare coupling `sqrt β = t`; use `t ≥ 1`. Geometry/radii native. See
  also exact statement `cool` for nonuniform exterior input; not a comparison theorem for
  the conditional density across different representations or perturbative orders by itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Cooling
open Function Filter MeasureTheory Lattice RG Wilson Tree Pressure Pressure.Stores Precision
open PatchArea Push.SectorMeasure Action
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f}

/-- Density *on the forest slice* at actual beta `t²`. All unmarked terms on the terminal step.
Constant (relative to both fields) removed. -/
def weight (F : Forest S.ratio) (V : Config G c) (t : ℝ) (U : F.Slice G) :=
  probative S (t^2) V (F.drape U)

def shock (F : Forest S.ratio) (R : Support c) (t : ℝ) (U : F.Slice G) := t^2 * total R (links S (F.drape U))

def depth (P : Patch) := belt P + belt P

section passage
variable (F : Forest S.ratio) (hs : InRange S) (R P : Support c) (V : Config G c) (t : ℝ)
  (hB : S.patch.Branches S.kernel G)
local notation "A" => lowerCost G S.patch S.kernel
local notation "B" => upperCost G S.patch S.kernel
local notation "J" => halo (belt S.patch) R

include hB
lemma weight_pass : Weight (F.order G) (weight F V t) := weight_of_pos
  (show Envelope (fun x=>probative S (t^2) V (F.drape x)) from envelope_comp (counted S hB V _) (F.continuous_drape.measurable))
    (fun U=> pulse S hB V _ (F.drape U))

omit hB
lemma bounded : Envelope (shock (G:=G) F R t) := by
  have he : Continuous (shock (G:=G) F R t) := by unfold shock total links; fun_prop
  exact ⟨he.measurable, he.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
lemma stays (U : F.Slice G) : shock F R t U ≤ t^2* (R.card * (linkRent S.patch * 4 : ℝ)) := by
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
  unfold total links; rw [total_at]; apply le_trans (Finset.sum_le_sum (g:=fun _=> (4:ℝ)) (by
    intro i _; simpa only [show (4:ℝ)= 2^2 by norm_num] using pow_le_pow_left₀ (G.chord_nonneg _) (G.chord_le_two (F.drape U i)) 2)) (le_of_eq ?_)
  rw [Finset.sum_const,nsmul_eq_mul, region_size S _ Axis]; unfold linkRent; push_cast; ring
lemma sdiff {x y : F.Slice G} (h : ∀ i, i∉located (area F) R → x i=y i) :
    shock F (P \ R) t y=shock F (P \ R) t x := by
  unfold shock
  refine congr_arg (t^2 * ·) (Finset.sum_congr rfl ?_); intro i he
  refine Finset.sum_congr rfl fun j hj=> ?_
  have he := fun hx:region S j = i => from_free S F h j (fun hk=> (Finset.mem_sdiff.mp he).2 (hx ▸ hk))
  rw [he (Finset.mem_singleton.mp (loc.mp hj))]
lemma fresh_bound {x : F.Slice G} (ht : 0<t) (hk : ∀ i∈located (area F) R, x i∈ G.shell t⁻¹) :
    shock F R t x ≤ R.card * (linkRent S.patch : ℝ) := by
  unfold shock total links; rw [total_at]
  have h(i) (h : i∈ located (region S) R) : G.chord (F.drape x i) ≤ t⁻¹ := by
    by_cases he:i∈ F.trunks; rw [show F.drape x i=1 from F.on_tree x ⟨i,he⟩, G.chord_one]; positivity
    rw [show F.drape x i=x ⟨i,he⟩ from F.off_tree x ⟨i,he⟩]; exact hk _ ((loc (a:=area F)).mpr ((loc (a:=region S)).mp h))
  rw [Finset.mul_sum]; refine (Finset.sum_le_sum (g:=fun _=>1) (fun i hi=>?_)).trans_eq ?_
  · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (G.chord_nonneg _) (h i hi) 2) (sq_nonneg _)).trans_eq (by rw [← mul_pow,mul_inv_cancel₀ ht.ne',one_pow])
  rw [Finset.sum_const,nsmul_eq_mul,mul_one,region_size S _ Axis]; unfold linkRent; push_cast; ring

-- keep also for nonuniform outer costs
include hs hB
def skyBill (S : StepData c f) (R : Support c) (V : Config G c) (t : ℝ) : ℝ :=
    t^2 * total R (outside V) + upperCost G S.patch S.kernel *
      (t^2 * total (halo (belt S.patch) R) (outside V)+ R.card * (linkRent S.patch:ℝ))

omit hB in
lemma hot (x : F.Slice G) : Real.exp (A⁻¹ * shock F R t x - t^2 * total R (outside V)) * weight F V t x ≤
    untapped S R (t^2) (F.drape x) V := by
  unfold weight probative untapped; rw [← opinion_scale]; apply opinion_mono; intro i ht
  rw [← Real.exp_add,total_split (halo (belt S.patch) R)]; apply Real.exp_monotone
  unfold shock; nlinarith only [mul_le_mul_of_nonneg_left (lower R F (fun i hi=> F.on_tree x ⟨i,hi⟩) hs ht V) (sq_nonneg t)]

omit hB in
lemma warmer {x : F.Slice G} : untapped S R (t^2) (F.drape x) V ≤
    Real.exp (B * (shock F (halo (depth S.patch) R) t x + t^2 * total J (outside V))) * weight F V t x := by
  unfold weight probative untapped; rw [← opinion_scale]; apply opinion_mono; intro i ht
  rw [← Real.exp_add, total_split (halo (belt S.patch) R)]; apply Real.exp_monotone; unfold shock
  have hv := (upper (halo (belt S.patch) R) F (fun i hi=> F.on_tree x ⟨i,hi⟩) hs ht V).trans (mul_le_mul_of_nonneg_left (add_le_add_left
      (total_mono (links_nn S _) (advance R _ _)) _) (zero_le_one.trans (Action.upper_pos G S.patch S.kernel)))
  unfold depth; nlinarith only [mul_le_mul_of_nonneg_left hv (sq_nonneg t)]
private lemma resampled {x y : F.Slice G} (ht : 0<t) (hk : ∀ i∈located (area F) R, y i∈G.shell t⁻¹) (hR : halo (depth S.patch) R⊆ P)
    (h : ∀ i, i ∉ located (area F) R → x i=y i) :
    Real.exp (A⁻¹ * shock F R t x - B * (shock F P t x - shock F R t x))*weight F V t x ≤
      Real.exp (skyBill S R V t) * weight F V t y := by
  let Y:= halo (depth S.patch) R
  let E:= B*(shock F (P\R) t x-t^2*(total R (outside V))/B)
  let b:=t^2*total R (outside V)
  let d:=B*(shock F Y t y + t^2*total J (outside V))
  have hp : untapped S R (t^2) (F.drape x) V ≤ Real.exp d * weight F V t y :=
    (far_charge S hB V (from_free S F h) _).trans_le (warmer F hs R V t)
  have hP := halo_subset (depth S.patch) R
  have hS (x : F.Slice G)(P : Support c)(hP:R⊆P) : shock F P t x-shock F R t x=shock F (P \ R) t x := by
    unfold shock; rw [← mul_sub]; exact congr_arg _ (Finset.sum_sdiff_eq_sub hP|>.symm)
  have hL : 0 < B := zero_lt_one.trans_le (Action.upper_pos G S.patch S.kernel)
  have hv : shock F Y t y ≤ R.card * (linkRent S.patch : ℝ)+shock F (P\R) t x := by
    rw [add_comm (_*_:ℝ), ← sdiff F R P t h]; refine le_trans (b:=shock F (Y\ R) t y+shock F R t y) ?_ (add_le_add (mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)) (fresh_bound F R t ht hk))
    · exact le_of_eq (sub_eq_iff_eq_add.mp (hS y Y hP))
    exact total_mono (links_nn _ _) (Finset.sdiff_subset_sdiff hR (Finset.Subset.refl _))
  rw [hS x P (hP.trans hR), show A⁻¹*_ - _= -E + (A⁻¹ * shock F R t x-b) by unfold E b; field_simp; ring, Real.exp_add,mul_assoc]
  refine (mul_le_mul_of_nonneg_left ((hot F hs R V t x).trans hp) (Real.exp_pos (-E)).le).trans ?_
  rw [← mul_assoc, ← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ ((weight_pass F V t hB).positive y)
  apply Real.exp_monotone; unfold d E skyBill; nlinarith only [mul_le_mul_of_nonneg_left hv hL.le, mul_div_cancel₀ (t^2*total R (outside V)) hL.ne'] -- check

def tax (G : Gauge) (P : Patch) (t : ℝ) := (linkRent P : ℝ) * Module.finrank ℝ G.Mat * Real.log (4*t)
omit hs hB in
lemma tax_pos (G : Gauge) (P : Patch) {t : ℝ} (ht : 1 ≤ t) : 0 ≤ tax G P t := by
  unfold tax; positivity [Real.log_nonneg (by linarith only [ht] : 1 ≤ 4*t)]

omit hs hB in
lemma shell_size (ht : 1 ≤ t) : Real.exp (- (R.card * tax G S.patch t)) ≤
                        (G.probHaar.real (G.shell t⁻¹))^(located (area F) R).card := by
  have hz : 1 ≤ 4*t := by linarith only [ht]
  have hT : 0<t:= lt_of_lt_of_le zero_lt_one ht
  let d:= Module.finrank ℝ G.Mat; let Z:=(located (area F) R).card
  let L:=linkRent S.patch
  have hp : (Z:ℝ)≤↑L*R.card := by exact_mod_cast free_size S R F
  refine le_trans ?_ (pow_le_pow_left₀ (pow_nonneg (show (0:ℝ)≤ t⁻¹/4 by positivity) d) (G.shell_ge _ (by positivity) (inv_le_one_of_one_le₀ ht)) Z)
  calc _ ≤ Real.exp ((Z:ℝ)*((d:ℝ)*(-Real.log (4*t)))) := by
             apply Real.exp_monotone; unfold tax; apply le_trans (b:= (↑L*R.card)*((d:ℝ)*(-Real.log (4*t)))) (le_of_eq ?_) (mul_le_mul_of_nonpos_right hp (mul_nonpos_of_nonneg_of_nonpos (by positivity) (neg_nonpos.mpr (Real.log_nonneg hz))))
             unfold d L; ring
       _ = _:=by rw [Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by positivity),mul_inv_rev]; simp [div_eq_mul_inv]

theorem jump (ht : 1 ≤ t) (he : halo (depth S.patch) R ⊆ P) : pressureBill (F.order G) (weight F V t)
      (fun x=> A⁻¹ * shock F R t x - B * (shock F P t x-shock F R t x)) ≤
          skyBill S R V t + R.card * tax G S.patch t := by
  exact erase_budget G.probHaar (located (area F) R) (G.shell_meas t⁻¹) (weight_pass F V t hB)
    (envelope_sub ((Envelope.const _).mul (bounded F R t)) ((Envelope.const _).mul (envelope_sub (bounded F P t) (bounded F R t)))) _ _ (shell_size F R t ht) (fun _ _ h h' => resampled F hs R P V t hB (zero_lt_one.trans_le ht) h' he h)

def regions (S : StepData c f) (R : Support c) (n : ℕ) := halo (n*depth S.patch) R
omit hs hB in
lemma renewal (S : StepData c f) (R : Support c) (n : ℕ) : halo (depth S.patch) (regions S R n)⊆ regions S R (n+1) := by
  unfold regions; rw [add_mul, one_mul]; exact advance R _ _

theorem cool (ht : 1 ≤ t) (W : ℝ) (p : ℕ)
    (he : ∀ n : ℕ,
      skyBill S (regions S R n) V t + (regions S R n).card * tax G S.patch t ≤ ((n:ℝ)+1)^p * W) :
    pressureBill (F.order G) (weight F V t) (fun x=> A⁻¹ * shock F R t x) ≤
        fee p A⁻¹ B * W := by
  let r := regions S R
  have hf := weight_pass F V t hB
  have ha : 0<A⁻¹:= inv_pos.mpr (by have := lower_pos G S.patch S.kernel; linarith)
  have hx (x : F.Slice G) {R P : Support c} (hR:R⊆P): shock F R t x≤shock F P t x:=
     mul_le_mul_of_nonneg_left (total_mono (links_nn _ _) hR) (sq_nonneg t)
  refine (pressure_mono hf ((Envelope.const _).mul (bounded F R t)) ((Envelope.const _).mul (bounded F (r 0) t))
     (fun x=> mul_le_mul_of_nonneg_left (hx x (halo_subset (0*depth S.patch) R)) ha.le)).trans ?_
  exact staircase hf (x:=fun n=> shock F (r n) t) (fun _=>bounded _ _ _) (fun n x=>(hx x (Finset.subset_univ _)).trans
    (stays F Finset.univ t x)) ha (zero_le_one.trans (upper_pos G S.patch S.kernel)) p (fun n=> (jump F hs _ _ V t hB ht (renewal S R n)).trans (he n))

def spread (G : Gauge) (S : Patch) (K : KernelChoices) (t L : ℝ) : ℝ := park (depth S) *
        (L + upperCost G S K * (park (belt S)*L + linkRent S) + tax G S t)
omit hs hB in
lemma spread_nn (G : Gauge) (P : Patch) (K : KernelChoices) (t L : ℝ) (ht : 1 ≤ t) (hl : 0 ≤ L) :
    0 ≤ spread G P K t L := by
  unfold spread; have h:=zero_le_one.trans (upper_pos G P K); positivity [h, park_nn (belt P), park_nn (depth P), tax_pos G P ht]
omit hB hs in
lemma priceSky (ht : 1≤t)(L : ℝ) (hl : 0 ≤ L) (hV : ∀ i:Site c,t^2 * outside V i ≤ L) (n:ℕ):
    skyBill S (regions S R n) V t+(regions S R n).card*tax G S.patch t ≤ ((n:ℝ)+1)^4 * (R.card * spread G S.patch S.kernel t L) := by
  let X:= regions S R n
  let a:= X.card; let b := R.card; let d:=depth S.patch; let Y:=halo (belt S.patch) X
  have hg(P:Support c): t^2 * total P (outside V)≤ P.card * L := by
    rw [← total_scale]; exact (Finset.sum_le_sum (s:=P) (fun i _=> hV i)).trans_eq (total_const P L)
  have hh : (Y.card:ℝ) ≤ a * park (belt S.patch):= by
    unfold a park; exact_mod_cast Lattice.Corona.halo_size X (belt S.patch)
  let D:= park d
  have he : (a:ℝ) ≤ b * D * ((n:ℝ)+1)^4:= by
    apply le_trans (b:=b*park (n*d)); unfold a b park; exact_mod_cast Lattice.Corona.halo_size R (n*d)
    unfold D park; rw [mul_assoc, ← mul_pow]; gcongr; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) d]
  let l:ℝ:=linkRent S.patch; let f:= tax G S.patch t
  have hx : 0≤ B:= zero_le_one.trans (upper_pos G S.patch S.kernel)
  have hy := add_le_add (hg X) (mul_le_mul_of_nonneg_left (add_le_add_left ((hg Y).trans (mul_le_mul_of_nonneg_right hh hl)) ((a:ℝ)*l)) hx)
  let m:=L+B*(park (belt S.patch)*L+l)+f
  have hp : 0≤m:=by unfold m l f; positivity [tax_pos G S.patch ht,park_nn (belt S.patch)]
  change t^2 * total X (outside V) + B*(t^2 * total Y (outside V)+ a*l) + a*f ≤ _
  refine (add_le_add_left hy ((a:ℝ)*f)).trans ?_
  calc _ = a*m := by unfold m; ring
       _ ≤ _ := le_trans (mul_le_mul_of_nonneg_right he hp) (le_of_eq (by change _=((n:ℝ)+1)^4*(b*(D*m)); ring))

theorem front (ht : 1 ≤ t) (L : ℝ) (hl : 0 ≤ L) (hV : ∀ i:Site c,t^2 * outside V i ≤ L) :
    pressureBill (F.order G) (weight F V t) (fun x=> A⁻¹ * shock F R t x) ≤
        fee 4 A⁻¹ B * (R.card * spread G S.patch S.kernel t L) := cool F hs R V t hB ht _ _ (priceSky (S:=S) R V t ht L hl hV)
end passage
end YM.MatchingLedger.Cooling

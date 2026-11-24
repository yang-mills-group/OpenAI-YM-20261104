import YM.MatchingLedger.Periodical.Lights

/-!
# One-link passage on the real patch. Haar included.

Door conditions imposed only on the remaining coordinates INSIDE the indicated support R. At
this stage any access spanning the port and queried link (proved by `consecutive`, `has_address`).
Far from that no frozen-cost hypothesis. Don't lose normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices) (hB : S.patch.Branches S.kernel G)
    (A : ChartRatio G) (Y : Chip (Page G c))

section replacement

variable (t : ℝ) (i : Needle F G) (R : Support c)
local notation "I" => Sum.inl i
local notation "D" => depot F (Sum.inl i)

def slip (U : F.Slice G) (i : F.Free)(x : G.Color) : F.Slice G := update U i (G.lieExp x)
def vacant (U : F.Slice G) (i : F.Free)(r : ℝ)(R:Support c) := ∀ j:F.Free,j ≠ i → area F j∈R → U j∈sector G r
lemma has_address (he: arc F (.inl i)⊆ R) : area F i.1∈R:= he (halo_subset _ {nest F i} (Finset.mem_singleton_self _))
variable {t i R}
lemma isField {U : F.Slice G} {x : G.Color}{r : ℝ}{i : F.Free}(hr : x∈ball 0 r) (hg : vacant F U i r R) : slip F U i x∈fieldTest F R r := by
  intro j hj; unfold slip; by_cases he:j=i; subst j; rw [Function.update_self]; exact stepZone hr; rw [Function.update_of_ne he]; exact hg _ he hj
lemma restores {U : F.Slice G}{x:G.El}{r : ℝ}{i : F.Free}(he:update U i x∈ fieldTest F R r) : vacant F U i r R:= by intro j hj hv; have hh:= he j hv; rwa [Function.update_of_ne hj] at hh

include hB in
lemma tapped (t : ℝ)(U : F.Slice G)(x:G.El): untapped S {nest F i} (t^2) (F.drape (Function.update U i.1 x)) (runway Y)=
    untapped S {nest F i} (t^2) (F.drape U) (runway Y):= far_charge S hB _ (from_free S F fun j hj=> Function.update_of_ne (fun he:j= i.1=>hj (by rw [he]; exact loc.mpr (Finset.mem_singleton_self (nest F i)))) ..) _

-- supplement to log Haar. At every slip read, weights include all branches before factoring
-- derivative of assembled near sum. Definition σ includes the queries' entire depot.
def sat (t : ℝ)(i : Needle F G)(v : Chip (Meter F G)) := t^2 * ∑ z ∈ depot F (Sum.inl i), dues S F G s z v
                                                        - ∑ z∈depot F (Sum.inl i), salary F A z v

lemma salary_amount (Q : Support c) (i : Needle F G) (he: arc F (Sum.inl i) ⊆ R)
    (_hQ : Q=depot F (Sum.inl i))(x : F.Slice G) :
    (∑ z∈Q, salary F A z (column F A Y R x))=∑ j∈located (area F) Q, jac A (boxLog A (x j)):=by
  unfold salary; rw [total_at]; apply Finset.sum_congr rfl; intro j hj
  change jac A ((tint G _ (stage F A R x)) j)=_; apply congr_arg (jac A); apply stage_inside
  have h:j ∈ located (area F) (depot F (Sum.inl i)) := _hQ ▸ hj
  exact he (Lattice.Corona.halo_mono (show belt S.patch ≤ stretch S.patch from by unfold stretch; omega) (Finset.Subset.refl _) (loc.mp h))

variable {A}
section chart
variable {U : F.Slice G}{n : ℕ}(H : Budget G A n){r : ℝ} (hr:r ≤ dial A)(hY:‖Y‖≤r) (hh:r≤H.space S.patch S.kernel) (he:arc F (.inl i)⊆R)
    (hf:vacant F U i.1 r R) (x:G.Color)(hx:x∈ball 0 r)
include hf hx hB hY he hr hh

def packCost (t : ℝ) (A : ChartRatio G)(U : F.Slice G) (i: Needle F G) : ℝ:= A.scale * (untapped S {nest F i} (t^2) (F.drape U) (runway Y)) * Real.exp (-(∑ j∈ (located (area F) (depot F (.inl i))).erase i.1, jac A (boxLog A (U j))))
lemma conditions (t : ℝ) :
      (A.scale*A.J x)* Cooling.weight F (runway Y) t (slip F U i.1 x)=
        packCost F Y t A U i * Real.exp (-(sat F s A t i (column F A Y R (slip F U i.1 x)))) := by
  let a: F.Free:= i.1; let W:= slip F U a x; let p:= located (area F) (depot F (.inl i))
  change _ * Cooling.weight F _ _ W=_*Real.exp (-(sat F s A t i (column F A Y R W)))
  have hW : W∈fieldTest F R r:= isField F hx hf
  rw [chart_amount F s hB Y hr H i hW hY hh he,show untapped S {nest F i} (t^2) (F.drape W) (runway Y)=_ from tapped (i:=i) F hB Y t U (G.lieExp x), sat, salary_amount F A Y D i he rfl W]
  let b:= ∑ j∈p.erase a, jac A (boxLog A (U j))
  have hP : a∈ p := loc.mpr (halo_subset _ {nest F i} (Finset.mem_singleton_self _))
  have hx': x∈ball 0 A.radius:= ball_subset_ball (hr.trans (cuts H.right).le) hx
  have hs : (∑ j∈p, jac A (boxLog A (W j)))= jac A x+b := by
    rw [← Finset.add_sum_erase p (fun j=> _) hP]
    rw [show W a=G.lieExp x from Function.update_self ..,aboard hr hx]; apply congr_arg (jac A x+·); exact Finset.sum_congr rfl fun j hj=> by rw [show W j= U j from Function.update_of_ne (Finset.ne_of_mem_erase hj) ..]
  let y:= t^2*∑ z∈depot F (.inl i), dues S F G s z (column F A Y R W)
  rw [hs,neg_mul]; unfold packCost; rw [mul_assoc (_*_ : ℝ), ← Real.exp_add]; change _*_*(Real.exp (-y)*_)= _*_ * Real.exp (-b+ -(y-(jac A x+b)))
  rw [show -b+ -(y-(jac A x+b))= jac A x+ -y by ring, Real.exp_add, jac, Real.exp_log (H.right.pos x hx')]; ring
end chart
end replacement

section slope
variable (A : ChartRatio G) (U : F.Slice G) (i : Needle F G)(v : G.Color)
-- along slip chart exact x derivatives for *any* fixed remaining fields.
def pluck (j : G.ColorIndex) := EuclideanSpace.basisFun G.ColorIndex ℝ j
lemma grain (j : G.ColorIndex) : ‖pluck (G:=G) j‖=1:=OrthonormalBasis.norm_eq_one ..
def hunch (G:Gauge) {ι : Type} [Fintype ι][DecidableEq ι](i : ι) := (tint G ι).symm.toContinuousLinearMap.comp (ContinuousLinearMap.single (R:=ℝ) (φ:=fun _ : ι=>G.Color) i)
lemma hunch_apply {ι : Type} [Fintype ι][DecidableEq ι] (j : ι)(x y : G.Color) (Y : ι×G.ColorIndex) :
    hunch G j (x+y) Y= if Y.1=j then x Y.2+y Y.2 else 0 := by change (Pi.single (M:=fun _ : ι=>G.Color) j (x+y) Y.1).ofLp Y.2=_; rw [Pi.single_apply]; split <;> rfl -- maybe binder order
lemma stride : hunch G i.1 (pluck (G:=G) i.2)=axis i:= by
  rw [show pluck (G:=G) i.2=EuclideanSpace.single i.2 1 from EuclideanSpace.basisFun_apply ..]
  ext j; rw [← add_zero (EuclideanSpace.single i.2 1), hunch_apply (G:=G)]; rcases i with ⟨u,j'⟩; rcases j with ⟨v,j⟩; simp only [axis_part, Prod.mk.injEq]; by_cases hv:v=u <;> by_cases he:j=j' <;> simp [hv,he]

variable {A v}{r : ℝ}{R : Support c}(hx:v∈ball 0 r)(hr:r≤dial A)(he:arc F (.inl i)⊆R)

include hx hr
private lemma line {y:G.Color} (hy:y∈ball 0 r):
    crawl F A (slip F U i.1 y)= crawl F A (slip F U i.1 v)+ hunch G i.1 (y-v) := by
  ext j; rw [Pi.add_apply]; rw [at_stage,at_stage]; unfold slip
  by_cases hh : j.1 = i.1
  · simp_rw [hh,Function.update_self, aboard hr hx,aboard hr hy]
    rw [← add_zero (y-v),hunch_apply (G:=G) _ _ _ j,if_pos hh]; change y.ofLp _=v.ofLp j.2+(y.ofLp j.2-v.ofLp j.2+(0:ℝ)); ring
  rw [Function.update_of_ne hh,Function.update_of_ne hh,← add_zero (y-v),hunch_apply (G:=G) _ _ _ j,if_neg hh,add_zero]

lemma crawl_line : ContDiffAt ℝ ω (fun z=>crawl F A (slip F U i.1 z)) v ∧
    HasFDerivAt (fun z=>crawl F A (slip F U i.1 z)) (hunch G i.1) v := by
  let f(z):= hunch G i.1 (z-v); let X:= crawl F A (slip F U i.1 v); let g(z):=X+f z
  have hm : ContDiff ℝ ω g := by unfold g f; fun_prop
  have ht : HasFDerivAt g (hunch G i.1) v := by
    have he := (hunch G i.1).hasFDerivAt.comp (f:=fun z=>z-v) v ((hasFDerivAt_id v).sub_const v); exact (he.const_add X)
  have hp : (fun z=>crawl F A (slip F U i.1 z)) =ᶠ[𝓝 v] g:=by
    filter_upwards [isOpen_ball.mem_nhds hx] with j hj; exact line F U i hx hr hj
  exact ⟨hm.contDiffAt.congr_of_eventuallyEq hp, ht.congr_of_eventuallyEq hp⟩

variable (R)
def reaches : G.Color →L[ℝ] Chip (Meter F G) := climb.comp ((cropMap (located (nest (G:=G) F) R)).comp (hunch G i.1))
variable {R}
include he in
omit hx hr in
lemma strides : reaches F i R (pluck (G:=G) i.2)=axis (Sum.inl i) := by
  unfold reaches; rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply, stride]
  rw [← needle_axis F i]; congr 1
  rw [crop_true]; ext j; rw [crop_apply]; split; rfl
  rename_i h; rw [axis_part]; split_ifs with hm; subst j; exact False.elim (h (loc.mpr (has_address F i R he))); rfl

lemma gut : ContDiffAt ℝ ω (fun z=>column F A Y R (slip F U i.1 z)) v ∧
    HasFDerivAt (fun z=>column F A Y R (slip F U i.1 z)) (reaches F i R) v := by
  obtain ⟨hp,hv⟩:= crawl_line F U i hx hr
  let k := climb (α:=Page G c) ∘L cropMap (located (nest (G:=G) F) R); let f(z):= crawl F A (slip F U i.1 z); let h:=descend (ι:=Needle F G) Y
  unfold column stage; simp_rw [pieces, ← crop_true]; change _ ∧ HasFDerivAt (fun z=> k (f z)+h) _ _
  exact ⟨(k.contDiff.contDiffAt.comp v hp).add contDiffAt_const,(k.hasFDerivAt.comp v hv).add_const h⟩
end slope
end YM.MatchingLedger.Periodical

import YM.Comparison.RG02.Assembly.Kernel
import YM.Comparison.RG02.Order.Restrict

/-!
# Compare true core-density expansion coefficients and joint Wick coefficients

Export the outputs before t-estimates at actual geometry. Compare also under narrowing the order
 or projected horizon, **without** recalibrating the source bases. Scale recoloring later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly
open Function Finset Filter MeasureTheory
open YM.Marker YM.Multi Order
open YM.PertExtension.Series YM.Comparison.RG02.Cumulants
open scoped Topology BigOperators Classical ContDiff

variable {V I S : Type} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype V] {R : Census V}
  [DecidableEq S] [Fintype S] {R' : Census S}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) (L : (I→ℝ)→ₗ[ℝ] E)
  (l : Hot R→ℕ) (F : Hot R→ E→ℂ) (f : E→ℝ)
variable (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (hv : Q.PosDef) {r : ℕ}
lemma prescription_unit : UnitLeading (prescription y L l F f Q hQ r) := by
  rw [UnitLeading,prescription,Cloud.prescribed,Cumulants.driven_quiet]; exact Cloud.wick_one ..

section
open YM.Next.SectorChange
local notation "μ" => Gaussian.cloud Q
variable [FiniteDimensional ℝ E]

-- the texture being integrated (no claim that this formula estimates the actual push at
-- asymptotic scale -- keep the separated estimates). Thermal moments for extraction.
def insideMoment (s : R.Mode) (j : ℕ) (z : I→ℝ) : ℂ := rows (expansions l F f) s j (translate y L z)
include hv
lemma gather (s : R.Mode) (t : Index r) :
    let q := insideMoment y L l F f s t.val.card
    Integrable q μ ∧
      (prescription y L l F f Q hQ r).part (Join.pair s t)= (t.val.card.factorial:ℂ)*∫ z,q z ∂μ := by
  obtain ⟨he,h⟩ := contracted y L l F f Q hQ hv r (Join.pair s t); intro q
  simp_rw [polarization] at *
  have ht : (t.val.card.factorial:ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  constructor
  · have hi := he.const_mul ((t.val.card.factorial:ℂ))⁻¹; simp_rw [inv_mul_cancel_left₀ ht] at hi; exact hi
  rw [h,integral_const_mul]; rfl

lemma order_read (s : R.Mode) {j : ℕ} (hj : j ≤ r) :
      (observe R r (prescription y L l F f Q hQ r) j).part s=∫ z,insideMoment y L l F f s j z ∂μ := by
  have hx := (gather y L l F f Q hQ hv s (pick r j)).2
  rw [picked r hj] at hx
  exact mul_left_cancel₀ (b:=_) (c:=_) (by exact_mod_cast (Nat.factorial_pos j).ne') ((observed (x:=prescription y L l F f Q hQ r) s hj).trans hx)

lemma prescription_sym : Order.Symmetric (prescription y L l F f Q hQ r) :=
  symmetric_test (fun s p t he=> by rw [(gather y L l F f Q hQ hv s p).2,(gather y L l F f Q hQ hv s t).2,he])

def evaluated (r : ℕ) (t : ℂ) (x : E) := value t (series R r (expansions l F f x))
lemma moment_integral (r : ℕ) (a : ℂ) (s : R.Mode) :
    let g := fun z:I→ℝ=> (evaluated l F f r a (translate y L z)).part s
    Integrable g μ ∧
      (value a (prescription y L l F f Q hQ r)).part s= ∫ z,g z ∂μ := by
  intro g; let m n z := a^n*insideMoment y L l F f s n z
  have hp i (hi : i∈range (r+1)) := show Integrable (m i) μ from (((picked r (by simpa using hi)).symm ▸ (gather y L l F f Q hQ hv s (pick r i)).1) : Integrable (insideMoment y L l F f s i) μ).const_mul (a^i)
  have hg z : g z=∑ i∈range (r+1),m i z := by
    unfold g evaluated; rw [vpart]; apply Finset.sum_congr rfl; intro i hi; rw [observation _ _ _ (by simpa using hi)]; rfl
  rw [funext hg]; refine ⟨integrable_finsetSum _ hp,?_⟩
  rw [integral_finsetSum _ hp,vpart]; unfold m; refine Finset.sum_congr rfl fun i hi=> ?_; rw [integral_const_mul,order_read y L l F f Q hQ hv s (by simpa using hi)]
end


section Compatible

-- Order/horizon restriction. Use matching of finite Taylor jets; higher packets spending
-- additional orders can keep the values used on the lower horizon. F vs F' may be different
-- germs if they actually have matching low orders. The valuation of `l` and `l'` can even
-- differ (ensure admissibilities separately). No statement on true remainder.
variable {r' : ℕ} (u : Extra.Trajectories.Names R R') (e : Fin r ↪ Fin r')
variable (l' : Hot R'→ℕ) (F' : Hot R'→E→ℂ) (f' : E→ℝ)
variable (h : ∀ j≤r,∀ x,vacuumLetter f' x j=vacuumLetter f x j)
    (h' : ∀ (i : Hot R),∀ j≤r,∀ x, markLetter l' F' (u.look i) x j=markLetter l F i x j)
include h h'
protected lemma compatible (x : E) : truncate u e (series R' r' (affine l' F' f' x))=series R r (affine l F f x) := by
  rw [trunc_series]; apply Join.both_parts; intro s t; rw [polarization,polarization]
  have hs := order_limit r t
  simp only [affine,map_add,Poly.part_plus,PowerSeries.coeff_map,part_restrict,
    realCoeff,h _ hs x, curve,PowerSeries.coeff_mk]
  by_cases hx : s=R.quiet
  · subst s; simp_rw [u.quiet,part_lit_quiet]; simp [beads]
  obtain ht := (hot_iff_ne s).2 hx
  let i : Multi.Hot R:= ⟨s,ht⟩
  have he : u.share s ≠ R'.quiet := fun hw=> hx (u.inj (hw.trans u.quiet.symm))
  have hw (q : Hot R→ℂ): (lit R q).part s=q i:= part_lit q i
  have hL (q : Hot R'→ℂ) : (lit R' q).part (u.share s)=q (u.look i):= part_lit q (u.look i)
  rw [beads,beads,if_neg he,if_neg hx,hL,hw,h' _ _ hs x]
include hv
variable [FiniteDimensional ℝ E]
lemma restriction : truncate u e (prescription y L l' F' f' Q hQ r')=prescription y L l F f Q hQ r := by
  ext t; rw [truncate, part_restrict, (contracted y L l' F' f' Q hQ hv ..).2, (contracted y L l F f Q hQ hv ..).2]
  apply integral_congr_ae
  filter_upwards with z
  rw [exponent_identity,exponent_identity,← part_restrict, Extra.Trajectories.Names.pass_restrict (Join.sub u (indexNames e)) (driver_quiet ..)]
  have H := Assembly.compatible l F f u e l' F' f' h h' (translate y L z)
  exact congrArg (fun p=> (Poly.pass p).part t) H
end Compatible
end YM.Comparison.RG02.Assembly

import YM.SchemeConversionRG11.Maxwell.Heart

/-! # Extract real isometry from the metric contractions with fixed squares

A true shared map for a whole (even infinite) input family, on shell variables.
Before applying the connected-component check. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set
open MvPolynomial hiding monomial
open scoped Topology BigOperators RealInnerProductSpace ComplexOrder
variable {G : Gauge}
abbrev Door (G : Gauge) := G.Color →L[ℝ] G.Color

def commerce (L : Door G) (A : TaylorTower G) : TaylorTower G := fun i ↦ faceMap i L (A i)
lemma commerce_comp (L R : Door G) (A : TaylorTower G) : commerce (L ∘L R) A = commerce L (commerce R A) := by
  funext i; apply Subtype.ext; funext u v; apply ContinuousMultilinearMap.ext; intro z; rfl
lemma commerce_id (A : TaylorTower G) : commerce (1 : Door G) A=A := funext fun _ ↦ Subtype.ext rfl

lemma givens {k : ℕ} (p : Flavor k) (A : Shell G k) (L : Door G) : available (faceMap k L A) p=L (available A p) := by
  have hw (i : G.ColorIndex) : faceMap k (cp i) (faceMap k L A)= ∑ j : G.ColorIndex, L (unitColor G j) i • faceMap _ (cp j) A := by
    apply Subtype.ext; rw [AddSubmonoidClass.coe_finsetSum]; funext a b; ext1 u; simp only [SetLike.val_smul,Finset.sum_apply,Pi.smul_apply, sum_apply,smul_apply]
    change L (A.val a b u) i = _
    conv_lhs => rw [← color_sum (A.val a b u) (G:=G),map_sum]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,map_smul, PiLp.smul_apply]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm ..
  ext1 i; change p (faceMap _ _ _) = _
  rw [hw]; conv_rhs => rw [← color_sum (available A p),map_sum]
  simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm ..
lemma shot_team (p : Flavor 0) (L : Door G) (A : TaylorTower G) : Maxwell.probe (commerce L A) (team G p p) = ((‖L (available (A 0) p)‖^2:ℝ):ℂ) := by
  rw [basicTeam, real_inner_self_eq_norm_sq,commerce, givens]
lemma shot_norm {L : Door G} (h : ∀ (p : Flavor 0) (A : TaylorTower G), Maxwell.probe (commerce L A) (team G p p)=Maxwell.probe A (team G p p)) : ∀ x:G.Color, ‖L x‖=‖x‖ := by
  intro x
  let P := cell 0 1
  let A : TaylorTower G := Pi.single 0 (fill 0 x (blade 0 1 1))
  have hx : available (A 0) P=x := by
    unfold A; rw [Pi.single_eq_same]; ext1 i
    change cell 0 1 (faceMap _ (cp (G:=G) i) (fill (G:=G) 0 x (blade 0 1 1))) =_
    rw [which,map_smul,cell_price]; norm_num [wedge,Matrix.one_apply]
  have hh := h P A; rw [shot_team P L, basicTeam, real_inner_self_eq_norm_sq,hx] at hh
  have he := Complex.ofReal_injective hh; nlinarith [norm_nonneg x,norm_nonneg (L x)]

def east (G : Gauge) : Studio G := WithLp.toLp _ fun i ↦ if i.1=i.2 then 1 else 0
lemma ready (G : Gauge) : graphL (east G)=1 := by
  ext1 v; rw [graph_eq]; change _=v; rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i : G.ColorIndex,v i • unitColor G i := Finset.sum_congr rfl fun i _ ↦ by simp [east]
    _ = _ := color_sum v
lemma retina_spray (b : Studio G) (A : TaylorTower G) (p : WickPol G) : retina b (spray A p) = Maxwell.probe (commerce (graphL b) A) p := spray_read b A p
lemma wall_visible (A : TaylorTower G) (p : WickPol G) (h : realForm p=p) : realWall (spray A p) := by
  intro b
  rw [retina_spray]; let X := commerce (graphL b) A
  let z := Maxwell.probe X p
  have ht : z=star z := by rw [show z=star z ↔ _ from Iff.rfl]; exact (congr_arg (Maxwell.probe X) h.symm).trans (real_eval ..)
  have he := Complex.ext_iff.mp ht |>.2
  change z.im= -z.im at he
  apply Complex.ext; exacts [rfl, (show (0:ℝ)=z.im by linarith)]

def duelP : Bool → ℂ := fun b ↦ if b then -1 else 1
def duelW {n : ℕ} (W U : Fin n → WickPol G) : Panel Bool n G := fun b ↦ if b then U else W
lemma tribute {n : ℕ} {W U : Fin n → WickPol G} (C₀ : G.ColorIndex) (h : Muted duelP (duelW W U)) (A : Fin n → TaylorTower G) (r : ℝ) :
    mean (Pct G) r (∏ i,spray (A i) (W i))=mean (Pct G) r (∏ i,spray (A i) (U i)) := by
  have hm := snowfall r C₀ duelP (duelW W U) h A
  simp only [snow,Fintype.sum_bool,duelW,duelP, Bool.false_eq_true,↓reduceIte,neg_smul,one_smul,map_add,map_neg] at hm; exact neg_add_eq_zero.mp hm |>.symm -- orientation

variable {ι : Type*} {W U : ι → WickPol G} (C₀ : G.ColorIndex)

include C₀
lemma tribute_poly {r : ℝ} (H : ∀ (n : ℕ) (i : Fin n→ι), Muted duelP (duelW (W ∘ i) (U ∘ i))) (A : ι→TaylorTower G) (p : MvPolynomial ι ℂ) :
    mean (Pct G) r (aeval (fun i ↦ spray (A i) (W i)) p)=mean (Pct G) r (aeval (fun i ↦ spray (A i) (U i)) p) := by
  induction p using MvPolynomial.induction_on' with
  | add _ _ h g => rw [map_add,map_add,map_add,map_add,h,g]
  | monomial d t =>
    obtain ⟨l,hh,_,_⟩ := mon_list d; simp only [MvPolynomial.coe_basisMonomials] at hh
    have he : MvPolynomial.monomial d (1:ℂ) = ∏ i:Fin l.length,X (l.get i) := by rw [hh, ← List.prod_ofFn, show (fun i => X (l.get i))= (X (R:=ℂ)) ∘ l.get from rfl,← List.map_ofFn, List.ofFn_get]
    have hx (U : ι→ WickPol G) : aeval (fun i ↦ spray (A i) (U i)) (MvPolynomial.monomial d t)=t • ∏ k:Fin l.length,spray (A (l.get k)) (U (l.get k)) := by
      rw [show MvPolynomial.monomial d t=t • MvPolynomial.monomial d 1 by simp [MvPolynomial.smul_monomial],map_smul,he,map_prod]; simp_rw [aeval_X]
    rw [hx,hx,map_smul,map_smul]
    exact congr_arg (t • ·) (tribute C₀ (H _ l.get) (A ∘ l.get) r)

theorem force_orthogonal
    (hW : ∀ i, realForm (W i)=W i) (hU : ∀ i, realForm (U i)=U i)
    (H : ∀ (n : ℕ) (i : Fin n→ι), Muted duelP (duelW (W ∘ i) (U ∘ i)))
    (ht : ∀ r : Flavor 0,∃ i, W i=team G r r ∧ U i=W i) :
    ∃ T : G.Color≃ₗᵢ[ℝ] G.Color, ∀ (p : TaylorTower G) i,
      Maxwell.probe (commerce T.toContinuousLinearEquiv.toContinuousLinearMap p) (U i)=Maxwell.probe p (W i) := by
  let B := ι×TaylorTower G
  let S (i:B) := spray i.2 (W i.1)
  let T (i:B) := spray i.2 (U i.1)
  obtain ⟨z,_,hz⟩ := coincides (show east G ∈ ball 0 (‖east G‖+1) by simp)
    (S:=S) (S':=T) (fun i ↦ wall_visible _ _ (hW _)) (fun i ↦ wall_visible _ _ (hU _))
    (fun p ↦ tribute_poly C₀ (W:=W ∘ Prod.fst) (U:=U ∘ Prod.fst) (fun n i ↦ H n (Prod.fst ∘ i)) Prod.snd p)
  let L := graphL z
  have he (p : TaylorTower G) (i : ι) : Maxwell.probe (commerce L p) (U i)=Maxwell.probe p (W i) := by
    have hp := hz ((i,p) : B); unfold T S at hp; simp only [retina_spray,ready,commerce_id] at hp; exact hp
  let R : G.Color→ₗᵢ[ℝ] G.Color := ⟨L.toLinearMap, shot_norm (fun r p ↦ by obtain ⟨i,hi,hU⟩ := ht r; rw [← hi]; exact (hU ▸ he p i))⟩
  refine ⟨R.toLinearIsometryEquiv rfl, fun p i ↦ ?_⟩
  rw [show (R.toLinearIsometryEquiv rfl).toContinuousLinearEquiv.toContinuousLinearMap=L from ContinuousLinearMap.ext fun v ↦ R.toLinearIsometryEquiv_apply rfl v]
  exact he p i

end YM.SchemeConversionRG11.Corona

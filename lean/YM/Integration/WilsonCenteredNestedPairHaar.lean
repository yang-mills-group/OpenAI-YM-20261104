import YM.Integration.WilsonCenteredNestedRootMean
import YM.Integration.WilsonCenteredNestedChildEdit

/-! The root average is taken once for the complete finite pair
of deposited vertices, including the real branch.  Its public endpoint
is the actual sum over all intermediate grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPairHaar
open Set Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom MeasureTheory
open OPE.Log OPE.Prescription WilsonCenteredNestedRawRows WilsonCenteredNestedRawPair
open WilsonCenteredNestedChildEdit WilsonCenteredNestedRealOrbit WilsonCenteredNestedRootMean
open WilsonCenteredNestedGross WilsonCenteredNestedLoggedRow WilsonCenteredNestedEdge
open scoped Classical Topology BigOperators
attribute [local instance] measO borelO YM.Work.A15.compact_ortho
local instance : IsProbabilityMeasure haar := by unfold haar;apply IsProbabilityMeasure.mk;apply Measure.haarMeasure_self
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def mean (W : Ortho→Bool→ℂ) : ℂ :=
  (2:ℝ)⁻¹ • ((∫ k,W k false ∂haar) + ∫ k,W k true ∂haar)

lemma leaf {n : ℕ} (D m : ℕ) (c : Q.channels m) (v : Fin n→S.Tag) (x : Fin n→E4) (o : E4)
    (live : orbitMargin Q.port D x o) (b : Bool) : Integrable (fun k=>face F Q Q.port D m c x v o k b) haar := by
  let L := ((WilsonCenteredNestedProjectedShadow.read F Q m D c).toContinuousLinearMap).restrictScalars ℝ
  let J := (conjugateR F.room.kernel.spin D).toContinuousLinearMap
  cases b
  · exact L.integrable_comp (checkable F Q D x o live (voices v))
  · exact L.integrable_comp (J.integrable_comp (checkable F Q D x o live (bar F.room.kernel.spin (voices v))))

lemma deposited (D m : ℕ) (c : Q.channels m) (v : Fin 2→S.Tag) (far : S.Tag) (x y : Fin 2→E4) (o : E4)
    (live : orbitMargin Q.port m y o) :
    mean (exitRow F Q D m c v far x y o) = held F Q D m c v far x y o := by
  let X (t:Menu.Cut Q D) := express Q t.1.val t.2 x v (y 0)
  let Y (t:Menu.Cut Q D) (b:Bool)(k:Ortho) := face F Q Q.port m m c y (placed F Q t far) o k b
  have hi (b:Bool) (t:Menu.Cut Q D) := leaf F Q m m c (placed F Q t far) y o live b
  have row (b:Bool) : (∫k,exitRow F Q D m c v far x y o k b ∂haar) = ∑ t, X t * ∫k,Y t b k ∂haar := by
    unfold exitRow
    rw [integral_finsetSum _ (fun t _=>(hi b t).const_mul (X t))]
    exact Finset.sum_congr rfl fun t _=>integral_const_mul _ _
  unfold mean held
  rw [row,row,←Finset.sum_add_distrib,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have eqn := WilsonCenteredNestedRootMean.original F Q m c y o live (voices (placed F Q t far))
  change _ = X t * Q.coef m c y (voices (placed F Q t far)) o
  rw [eqn]
  change (2:ℝ)⁻¹ • (X t * _ + X t * _) = X t * ((2:ℝ)⁻¹ • (_ + _))
  rw [←mul_add,Algebra.mul_smul_comm]
  rfl

lemma difference (X Y : Ortho→Bool→ℂ) {E : ℝ} (pay : ∀ k b,‖X k b-Y k b‖ ≤ E)
    (mx : ∀b,AEStronglyMeasurable (fun k=>X k b) haar) (iy : ∀b,Integrable (fun k=>Y k b) haar) :
    ‖mean X - mean Y‖ ≤ E := by
  have idiff (b:Bool) : Integrable (fun k=>X k b - Y k b) haar :=
    (integrable_const E).mono' ((mx b).sub (iy b).aestronglyMeasurable) (ae_of_all _ (fun k=>pay k b))
  have ix (b:Bool) : Integrable (fun k=>X k b) haar := by
    have e := (idiff b).add (iy b)
    exact e.congr (ae_of_all _ fun k=>show X k b-Y k b+Y k b=X k b from sub_add_cancel ..)
  have hr (b:Bool) : ‖(∫k,X k b ∂haar) - ∫k,Y k b ∂haar‖ ≤ E := by
    rw [←integral_sub (ix b) (iy b)]
    simpa using norm_integral_le_of_norm_le_const (μ:=haar) (ae_of_all _ (fun k=>pay k b))
  unfold mean
  rw [←smul_sub,show (∫ k,X k false ∂haar)+(∫ k,X k true ∂haar) -
    ((∫ k,Y k false ∂haar)+(∫ k,Y k true ∂haar)) =
    ((∫ k,X k false ∂haar)-(∫ k,Y k false ∂haar))+((∫ k,X k true ∂haar)-(∫ k,Y k true ∂haar)) by abel,norm_smul]
  calc
    _ ≤ ‖(2:ℝ)⁻¹‖ * (E+E) := mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add (hr false) (hr true))) (norm_nonneg _)
    _ = _ := by norm_num;ring

private lemma products {T : Type} [Fintype T] (X Y : T→Ortho→ℂ)
    (xi : ∀ t,Integrable (X t) haar) (yi : ∀ t,Integrable (Y t) haar) :
    AEStronglyMeasurable (fun k=>∑ t,X t k*Y t k) haar := by
  let W := fun t=>X t*Y t
  change AEStronglyMeasurable (fun k=>∑ t,W t k) haar
  simp only [←Finset.sum_apply]
  exact Finset.aestronglyMeasurable_sum _ (fun t _=>(xi t).aestronglyMeasurable.mul (yi t).aestronglyMeasurable)

private lemma portfolio {T : Type} [Fintype T] (a : T→ℂ) (Y : T→Ortho→ℂ) (yi : ∀ t,Integrable (Y t) haar) :
    Integrable (fun k=>∑ t,a t * Y t k) haar :=
  integrable_finsetSum (μ:=haar) (f:=fun t k=>a t *Y t k) Finset.univ (fun t _=>(yi t).const_mul _)

theorem original (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (D m : ℕ)
    (mc : Q.channels m) (v : Fin 2→S.Tag) (far : S.Tag) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(j l:ℕ)(A B:ℝ),0≤A ∧ 0≤B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ),0<a → a≤r →
      ∀(x y:Fin 2→E4)(o:E4),WithinRoom a M η x (y 0) → WithinRoom r M η y o →
      ‖mean (joined F Q Q.port D m m mc v far x y o) - held F Q D m mc v far x y o‖ ≤
        Fintype.card (Menu.Cut Q D) * (wage j A a * wage l B r * base a r m (degree v) far.1 * (a/r)^(D+1)) := by
  obtain ⟨j,l,A,B,An,Bn,earned⟩ := WilsonCenteredNestedChildEdit.original F Q fac foundation lo ticket D m mc v far Mn ηp
  have enter := Orbits.admissible_separated (I:=Fin 2) F Q Mn ηp D
  have exit := Orbits.admissible_separated (I:=Fin 2) F Q Mn ηp m
  obtain ⟨ε,εp,fine⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp enter
  refine ⟨j,l,A,B,An,Bn,?_⟩
  filter_upwards [earned,exit,mem_nhdsWithin_of_mem_nhds (ge_mem_nhds εp)] with r paid atR tight a ap ar x y o near farRoom
  have c₀ := fine (show a∈Ioc 0 ε from ⟨ap,ar.trans tight⟩) x (y 0) near D le_rfl
  have c₁ := atR y o farRoom m le_rfl
  rw [←deposited F Q D m mc v far x y o c₁]
  apply difference _ _ (paid a ap ar x y o near farRoom)
  · intro b
    apply products (T:=Menu.Cut Q D) (fun t k=>face F Q Q.port D t.1.val t.2 x v (y 0) k b)
      (fun t k=>face F Q Q.port m m mc y (placed F Q t far) o k b)
    · exact fun t=>leaf F Q D t.1.val t.2 v x (y 0) c₀ b
    · exact fun t=>leaf F Q m m mc (placed F Q t far) y o c₁ b
  · intro b
    apply portfolio (T:=Menu.Cut Q D) (fun t=>express Q t.1.val t.2 x v (y 0))
      (fun t k=>face F Q Q.port m m mc y (placed F Q t far) o k b)
    exact fun t=>leaf F Q m m mc (placed F Q t far) y o c₁ b

end YM.Integration.WilsonCenteredNestedPairHaar

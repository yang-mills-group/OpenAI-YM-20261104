import YM.Integration.FVA1Physical.Marked.InvariantOperand
import YM.Next.MAXWELL.Covariance

/-! Exact physical basis fields as finite lists of gauge-invariant native
RG atoms. Each rank is the degree of an actual supported monomial, so the
lower engineering grade and all path supports survive Haar averaging. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Finset Lattice RG YM.Wilson Source Stationary Next.Foundations MeasureTheory
open Qlocal.Quipu.Zora
open scoped Classical BigOperators
variable {G:Gauge} {m:ℕ}

private abbrev Mono (G:Gauge) (m:ℕ) := (Fin m × G.ColorIndex) →₀ ℕ
private def letters (v:Mono G m) : List (Fin m × G.ColorIndex) :=
  (Maxwell.Free.mon_list v).choose

private def orbitAtom (S:Fin m→RG.Slot) (v:Mono G m) : RG.Atom G (letters v).length :=
  ⟨fun j=>S ((letters v).get j).1,
   (Classical.choice (born G (letters v).length)).forecast (fun j=>((letters v).get j).2)⟩

private theorem orbit_legal (S:Fin m→RG.Slot) (v:Mono G m) : (orbitAtom S v).Invariant :=
  (Classical.choice (born G (letters v).length)).funded (fun j=>((letters v).get j).2) le_rfl

private def word (v:Mono G m) (p:Fin m → G.Color) : ℝ :=
  ∏ j:Fin (letters v).length, p ((letters v).get j).1 ((letters v).get j).2

private theorem spell (v:Mono G m) (p:Fin m → G.Color) :
    Bid.lumin ((MvPolynomial.basisMonomials _ ℂ) v) p = (word v p:ℂ) := by
  rw [(Maxwell.Free.mon_list v).choose_spec.1]
  let c := fun i:Fin m × G.ColorIndex => (p i.1 i.2:ℂ)
  change MvPolynomial.aeval c _ = _
  rw [map_list_prod]
  simp only [List.map_map,Function.comp_def,MvPolynomial.aeval_X]
  change ((letters v).map c).prod = (word v p : ℂ)
  rw [show ((letters v).map c).prod = ∏ j:Fin (letters v).length, c ((letters v).get j) from by
    calc
      _ = ((List.ofFn (letters v).get).map c).prod := by rw [List.ofFn_get]
      _ = (List.ofFn (c ∘ (letters v).get)).prod := congrArg List.prod (List.map_ofFn (g:=c) (f:=(letters v).get))
      _ = _ := List.prod_ofFn]
  simp only [word,Complex.ofReal_prod,c]

private theorem polynomial_words (P:Bid.Pose G m) (p:Fin m → G.Color) :
    Bid.lumin P p = ∑ v∈P.support, P.coeff v * (word v p:ℂ) := by
  let F : Bid.Pose G m →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun i:Fin m × G.ColorIndex => (p i.1 i.2:ℂ))
  change F P = _
  nth_rw 1 [P.as_sum]
  rw [map_sum]
  apply sum_congr rfl
  intro v _
  rw [show MvPolynomial.monomial v (P.coeff v)=
    MvPolynomial.C (P.coeff v) * (MvPolynomial.basisMonomials _ ℂ) v by
    simp only [MvPolynomial.coe_basisMonomials,MvPolynomial.C_mul_monomial, mul_one],map_mul]
  exact congrArg₂ (·*·) (MvPolynomial.aeval_C ..) (spell v p)

private theorem orbit_read (S:Fin m→RG.Slot) (v:Mono G m) {n:Side} (o:Site n) (U:Config G n) :
    (orbitAtom S v).unmasked U o =
      ∫ u:G.El, word v (fun j=>G.adjoint u ((S j).atSite U o)) ∂G.probHaar := by
  let Y := Classical.choice (born G (letters v).length)
  let j := fun i:Fin (letters v).length => ((letters v).get i).2
  let X := fun i:Fin (letters v).length => (S ((letters v).get i).1).atSite U o
  exact (Y.focused j X).trans (Y.hours j X le_rfl)

structure FieldAtom (G:Gauge) where
  rank : ℕ
  atom : RG.Atom G rank
  invariant : atom.Invariant
  factor : ℂ

/-- All the atoms are fixed before the period, position and independent
background. The equality holds on arbitrary group fields, with every slot
covered by the real physical stencil and its original grade retained. -/
theorem physical_field_atoms (d:ℕ) (i:((Labels.frames G).level d).Index) :
    ∃ t:ℕ, ∃ A:Fin t→FieldAtom G,
      (∀ j, (((Labels.frames G).level d).grades i).2 ≤ (A j).rank) ∧
      (∀ j l,((A j).atom.leg l).stencil ⊆ (localSection G d).stencil) ∧
      ∀ (n:Side) (o:Site n) (U:Config G n),
        (localSection G d).places (Pi.single i 1) o U =
        ∑ j,(A j).factor * (((A j).atom.unmasked U o:ℝ):ℂ) := by
  let a := Marked.squareBasis G d i
  let P := a.polynomial
  let J := P.support
  let row (v:Mono G a.arity) : FieldAtom G := ⟨(letters v).length,orbitAtom a.slot v,orbit_legal a.slot v,P.coeff v⟩
  let e := J.equivFin.symm
  refine ⟨J.card,(fun j=>row (e j).val),?_,?_,?_⟩
  · intro j
    exact ((Marked.square_basis_spec d i).2.1 (e j).val (e j).property).trans_eq
      (Maxwell.Free.mon_list (e j).val).choose_spec.2.2.symm
  · intro j l
    exact (Marked.square_basis_spec d i).1 _
  intro n o U
  let R := (localSection G d).places (Pi.single i 1) o
  let rot (u:G.El) : Fin a.arity → G.Color := fun h=>G.adjoint u ((a.slot h).atSite U o)
  have id (u:G.El) : ∑ v∈J, P.coeff v * (word v (rot u):ℂ) = R U := by
    rw [←polynomial_words]
    let W := gauge (fun _=>u) U
    have h := (Marked.square_basis_spec d i).2.2 n o W
    rw [(localSection G d).placed_invariant (sound G d) _ _ (fun _=>u) U] at h
    apply Eq.trans _ h.symm
    change Bid.lumin P (rot u) = Bid.lumin P _
    apply congrArg (Bid.lumin P)
    funext j
    exact (Work.F05.slot_gauge (a.slot j) U (fun _=>u) o).symm.trans (Work.F02.atSite_curvature (a.slot j) W o)
  have integ (v:Mono G a.arity) :
      Integrable (fun u:G.El=>P.coeff v*(word v (rot u):ℂ)) G.probHaar := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      (core_continuous (fun j:Fin (letters v).length=>((letters v).get j).2)
        (fun j=> (a.slot ((letters v).get j).1).atSite U o)))
  change R U = ∑ j, _
  calc
    R U = ∫ u:G.El, ∑ v∈J, P.coeff v*(word v (rot u):ℂ) ∂G.probHaar := by simp only [id,integral_const,probReal_univ,one_smul]
    _ = ∑ v∈J,P.coeff v*((orbitAtom a.slot v).unmasked U o:ℂ) := by
      rw [integral_finsetSum _ (fun v _=>integ v)]
      apply sum_congr rfl
      intro v _
      rw [integral_const_mul,integral_complex_ofReal,orbit_read]
    _ = _ := by
      rw [← Finset.sum_coe_sort J]
      exact (Equiv.sum_comp e _).symm

end YM.Integration.FVA1Physical.Round2.CP5

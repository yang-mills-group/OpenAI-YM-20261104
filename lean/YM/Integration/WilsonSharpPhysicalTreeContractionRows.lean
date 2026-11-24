import YM.Integration.WilsonCenteredNestedTerminalOrbit

/-! The two exact finite decompositions of a held Wilson vertex, and the
terminal cancellation on the actual signed raw factorization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeContractionRows
open Function Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedTerminalOrbit
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRealOrbit
open scoped Classical BigOperators ComplexConjugate
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I → ℕ}

abbrev Band (h : ℕ) := ↥(bands F.sector.derivatives h)

def physicalActor (h : ℕ) (a : Menu.Cut Q h) : S.Field h :=
  F.sector.derivatives.rise (Nat.le_of_lt_succ a.1.isLt) (Q.actor a.1 a.2)

theorem physicalFrame (h : ℕ) (v : S.Field h) :
    ∑ a : Menu.Cut Q h, read F Q a.1 h a.2 v • physicalActor F Q h a = v := by
  rw [Fintype.sum_sigma]
  exact assemble F Q h v

def rawActor (h : ℕ) (k : Ortho) (b : Bool) (w : Band F h) : S.Field h :=
  out F h k b (Q.port.loaded w.1 h)

private lemma scalar_add (b : Bool) (a c : ℂ) : scalar b (a+c) = scalar b a + scalar b c := by
  cases b <;> simp [scalar]

private lemma scalar_mul (b : Bool) (a c : ℂ) : scalar b (a*c) = scalar b a * scalar b c := by
  cases b <;> simp [scalar]

private lemma scalar_back (b : Bool) (a : ℂ) : scalar b (scalar b a) = a := by
  cases b <;> simp [scalar]

private lemma into_add (j : ℕ) (k : Ortho) (b : Bool) (v w : S.Field j) :
    into F j k b (v+w) = into F j k b v + into F j k b w := by
  cases b <;> simp [into]

private lemma into_smul (j : ℕ) (k : Ortho) (b : Bool) (a : ℂ) (v : S.Field j) :
    into F j k b (a • v) = scalar b a • into F j k b v := by
  cases b <;> simp [into, scalar, map_smulₛₗ]

def pulled (k : Ortho) (b : Bool) (v : Labels S d) : Labels S d :=
  fun i => into F (d i) k b (v i)

omit [Fintype I] in
private lemma pulled_update [DecidableEq I] (k : Ortho) (b : Bool) (v : Labels S d)
    (j : I) (u : S.Field (d j)) :
    pulled F k b (update v j u) = update (pulled F k b v) j (into F (d j) k b u) := by
  funext i
  by_cases e : i = j
  · subst j
    simp [pulled]
  · simp [pulled, update_of_ne e]

/-- The complex multilinear numerical row of one raw mode at a held rotor
and real branch. Its arguments are the actual resident fields. -/
def modeRow (w : Mode F.sector.derivatives) (x : I → E4) (o : E4) (k : Ortho) (b : Bool) :
    MultilinearMap ℂ (fun i => S.Field (d i)) ℂ := by
  let A : MultilinearMap ℂ (fun i => S.Field (d i)) ℂ :=
    checkRow Q.port w (Ortho.move k⁻¹ ∘ x) (Ortho.move k⁻¹ o)
  refine ⟨fun v => scalar b (A (pulled F k b v)), ?_, ?_⟩
  · intro dec v j a c
    cases Subsingleton.elim dec (Classical.decEq _)
    rw [pulled_update, into_add, A.map_update_add, ← pulled_update, ← pulled_update, scalar_add]
  · intro dec v j a c
    cases Subsingleton.elim dec (Classical.decEq _)
    rw [pulled_update, into_smul, A.map_update_smul, ← pulled_update]
    change scalar b (scalar b a * A (pulled F k b (update v j c))) = a * _
    rw [scalar_mul, scalar_back]

theorem modeRow_apply (w : Mode F.sector.derivatives) (x : I → E4) (o : E4)
    (k : Ortho) (b : Bool) (v : Labels S d) :
    modeRow F Q w x o k b v = scalar b (Q.port.ope w (Ortho.move k⁻¹ ∘ x)
      (names (pulled F k b v)) (Ortho.move k⁻¹ o)) := by
  change scalar b (checkRow Q.port w _ _ (pulled F k b v)) = _
  rw [check_eq Q.port w Q.continuum]

theorem rawFrame (h : ℕ) (x : I → E4) (o : E4) (k : Ortho) (b : Bool) (v : Labels S d) :
    ∑ w : Band F h, modeRow F Q w.1 x o k b v • rawActor F Q h k b w =
      restored F Q.port h x v o k b := by
  rw [currency, shadowOld, OPE.shadow, add_smul]
  change (∑ w : Band F h, modeRow F Q w.1 x o k b v • out F h k b (Q.port.loaded w.1 h)) = _
  simp only [modeRow_apply]
  exact Finset.sum_coe_sort (bands F.sector.derivatives h)
    (fun w => scalar b (Q.port.ope w (Ortho.move k⁻¹ ∘ x) (names (pulled F k b v))
      (Ortho.move k⁻¹ o)) • out F h k b (Q.port.loaded w h))

/-- The grade-m terminal reader deletes lower raw output modes after the
complete tree contraction, for the same unaveraged signed factorization. -/
theorem terminal (s : Arboreal I) (D : I → ℕ) (x : I → E4) (v : I → C.book.Token)
    (m : ℕ) (c : Q.channels m) (k : Ortho) (b : Bool) :
    read F Q m m c (out F m k b (∑ w ∈ bands F.sector.derivatives m,
      Arboreal.factorization Q.port s s.zones x v w D • Q.port.loaded w m)) =
    ∑ w ∈ (bands F.sector.derivatives m).filter (fun w => w.1 = m),
      scalar b (Arboreal.factorization Q.port s s.zones x v w D) *
        read F Q m m c (out F m k b (Q.port.loaded w m)) := by
  rw [add_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  symm
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro w hw missing
  have low : w.1 < m := lt_of_le_of_ne ((full_bands ..).mp hw)
    (fun e => missing (Finset.mem_filter.mpr ⟨hw,e⟩))
  rw [lower F Q c w low k b, mul_zero]

end YM.Integration.WilsonSharpPhysicalTreeContractionRows

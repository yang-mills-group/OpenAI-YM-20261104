import YM.Integration.WilsonSharpPhysicalTreeContractionFusion

/-! Identification of the complete physical contraction with the literal
signed raw factorization in the elected reader's logarithmic tree ticket. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeContractionFlat
open Function Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting WilsonCenteredNestedTerminalOrbit WilsonCenteredNestedProjectedShadow
open WilsonSharpPhysicalTreeContractionRows WilsonSharpPhysicalTreeContractionLayout
open WilsonSharpPhysicalTreeContractionFusion WilsonSharpPhysicalTreeGeometry YangMills.Hierarchy
open scoped Classical BigOperators ComplexConjugate
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (t : FusionTree)

def rawCaps (D : Fin t.branches → ℕ) : Node t → ℕ :=
  Sum.elim (Fin.cases 0 D) (fun _ => 0)

def leafNames (a : Fin t.leaves → S.Tag) (k : Ortho) (b : Bool) : Node t → C.book.Token :=
  Sum.elim (fun _ => quoteTag (⟨0,0⟩ : S.Tag))
    (fun i => quoteTag (⟨(a i).1, into F (a i).1 k b (a i).2⟩ : S.Tag))

abbrev Intermediate (D : Fin t.branches → ℕ) := (i : Fin t.branches) → Band F (D i)

def modeTuple (D : Fin t.branches → ℕ) (m : ℕ) (w : Band F m) (a : Intermediate F t D) :
    Modes F t D m := Fin.cases w a

def castLabels (D : Fin t.branches → ℕ) (m : ℕ) (w : Band F m) (a : Intermediate F t D) :
    Node t → Mode F.sector.derivatives :=
  Sum.elim (fun v => (modeTuple F t D m w a v).1) (fun _ => w.1)

private theorem rootOutside :
    (.inl 0 : Node t) ∉ (rawTree t).middle (rawTree t).zones :=
  fun h => ((proper_mem t _).mp h).1 rfl

private theorem leafOutside (i : Fin t.leaves) :
    (.inr i : Node t) ∉ (rawTree t).middle (rawTree t).zones :=
  fun h => zone_inr t i ((proper_mem t _).mp h).2

def castEquiv (D : Fin t.branches → ℕ) (m : ℕ) (w : Band F m) :
    Intermediate F t D ≃ ↥((rawTree t).casting (rawTree t).zones (rawCaps t D) w.1) where
  toFun a := ⟨castLabels F t D m w a, by
    rw [(rawTree t).casts]
    intro p
    cases p with
    | inl v =>
      refine Fin.cases ?_ (fun i => ?_) v
      · exact ⟨fun h => (rootOutside t h).elim, fun _ => rfl⟩
      · exact ⟨fun _ => (a i).2, fun h => (h (properEquiv t i).2).elim⟩
    | inr i => exact ⟨fun h => (leafOutside t i h).elim, fun _ => rfl⟩⟩
  invFun f i := ⟨f.1 (.inl i.succ),
    (((rawTree t).casts (rawTree t).zones w.1).mp f.2 (.inl i.succ)).1 (properEquiv t i).2⟩
  left_inv a := by funext i; apply Subtype.ext; rfl
  right_inv q := by
    apply Subtype.ext
    funext p
    have h := ((rawTree t).casts (rawTree t).zones w.1).mp q.2
    cases p with
    | inl v =>
      refine Fin.cases ?_ (fun _ => rfl) v
      exact ((h (.inl 0)).2 (rootOutside t)).symm
    | inr i => exact ((h (.inr i)).2 (leafOutside t i)).symm

theorem rawEvent (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (X : Node t → E4) (k : Ortho) (b : Bool) (w : Band F m) (j : Intermediate F t D)
    (v : t.Vertex) :
    localRow F Q t a D X k b v (modeTuple F t D m w j v).1
      (fun p => rawResident F Q t a D m k b (modeTuple F t D m w j) p.1) =
    scalar b (Arboreal.eventAt Q.port (rawTree t) (rawTree t).zones
      (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) (.inl v) (castLabels F t D m w j)) := by
  let e := childEquiv t v
  let kids := (rawTree t).kids (.inl v)
  let f := castLabels F t D m w j
  let old := Arboreal.audition Q.port (rawTree t).zones (leafNames F t a k b) f
  let fields (p : t.Child v) := rawResident F Q t a D m k b (modeTuple F t D m w j) p.1
  have fromSeat (p : t.Child v) : (Arboreal.crop old kids ∘ e) p = old (childNode t p.1) :=
    congrArg old (childEquiv_val t v p)
  have leafAud (i : Fin t.leaves) : old (.inr i) = leafNames F t a k b (.inr i) := by
    dsimp only [old, Arboreal.audition]
    rw [if_neg (zone_inr t i)]
  have branchAud (i : Fin t.branches) : old (.inl i.succ) = Q.port.letter (j i).1 := by
    dsimp only [old, Arboreal.audition]
    rw [if_pos (zone_inl t i.succ)]
    exact congrArg Q.port.letter (show f (.inl i.succ) = (j i).1 from rfl)
  have hm (p : t.Child v) : WilsonThermometerWeakPairRise.Move F.sector.derivatives
      ((Arboreal.crop old kids ∘ e) p) (names (pulled F k b fields) p) := by
    rw [fromSeat]
    obtain ⟨s, hs⟩ := p
    cases s with
    | inl i =>
      apply Or.inl
      exact (leafAud i).trans rfl
    | inr i =>
      change WilsonThermometerWeakPairRise.Move F.sector.derivatives (old (.inl i.succ)) _
      rw [branchAud i]
      change WilsonThermometerWeakPairRise.Move F.sector.derivatives (Q.port.letter (j i).1)
        ⟨D i, S.representative (D i) (into F (D i) k b (out F (D i) k b (Q.port.loaded (j i).1 (D i))))⟩
      rw [returns F Q]
      exact WilsonThermometerWeakPairRise.basis Q.port (j i)
  rw [localRow, modeRow_apply]
  apply congrArg (scalar b)
  let rawX := Arboreal.crop (Ortho.move k⁻¹ ∘ X) kids
  let o := Ortho.move k⁻¹ (X (.inl v))
  have seatEq := WilsonThermometerWeakPairRise.coefficient Q.port Q.spans
    Q.continuum.laws.toSymmetric Q.lifts hm (modeTuple F t D m w j v).1 (rawX ∘ e) o
  exact seatEq.symm.trans (Q.port.coefficient_perm (x := rawX) (z := o) (Arboreal.crop old kids)
    Q.continuum.laws.toSymmetric e (modeTuple F t D m w j v).1)

private lemma scalar_prod {I : Type} [Fintype I] (b : Bool) (c : I → ℂ) :
    (∏ i, scalar b (c i)) = scalar b (∏ i, c i) := by
  cases b <;> simp [scalar]

private lemma scalar_sum {I : Type} [Fintype I] (b : Bool) (c : I → ℂ) :
    (∑ i, scalar b (c i)) = scalar b (∑ i, c i) := by
  cases b <;> simp [scalar]

theorem rawEnsemble (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (X : Node t → E4) (k : Ortho) (b : Bool) (w : Band F m) (j : Intermediate F t D) :
    rawProduct F Q t a D m X k b (modeTuple F t D m w j) =
      scalar b (Arboreal.ensemble Q.port (rawTree t) (rawTree t).zones (Ortho.move k⁻¹ ∘ X)
        (leafNames F t a k b) (castLabels F t D m w j)) := by
  let V (n : Node t) := Arboreal.eventAt Q.port (rawTree t) (rawTree t).zones
    (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) n (castLabels F t D m w j)
  calc
    _ = ∏ v : t.Vertex, scalar b (V (.inl v)) :=
      Finset.prod_congr rfl (fun v _ => rawEvent F Q t a D m X k b w j v)
    _ = scalar b (∏ v : t.Vertex, V (.inl v)) := scalar_prod _ _
    _ = _ := congrArg (scalar b) <| calc
      _ = ∏ u : ↥(rawTree t).zones, V u.1 := (zoneEquiv t).prod_comp (fun u => V u.1)
      _ = _ := Finset.prod_coe_sort _ _

theorem castSum (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (X : Node t → E4) (k : Ortho) (b : Bool) (w : Band F m) :
    (∑ j : Intermediate F t D, rawProduct F Q t a D m X k b (modeTuple F t D m w j)) =
      scalar b (Arboreal.factorization Q.port (rawTree t) (rawTree t).zones (Ortho.move k⁻¹ ∘ X)
        (leafNames F t a k b) w.1 (rawCaps t D)) := by
  let s := rawTree t
  let V := Arboreal.ensemble Q.port s s.zones (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b)
  calc
    _ = ∑ j : Intermediate F t D, scalar b (V (castLabels F t D m w j)) :=
      Finset.sum_congr rfl (fun j _ => rawEnsemble F Q t a D m X k b w j)
    _ = scalar b (∑ j : Intermediate F t D, V (castLabels F t D m w j)) := scalar_sum _ _
    _ = _ := congrArg (scalar b) <| calc
      _ = ∑ u : ↥(s.casting s.zones (rawCaps t D) w.1), V u.1 :=
        Fintype.sum_equiv (castEquiv F t D m w) _ _ (fun _ => rfl)
      _ = _ := Finset.sum_coe_sort _ _

theorem factorizationAt (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (H : ℕ)
    (L : S.Field H →ₗ[ℂ] ℂ) (X : Node t → E4) (k : Ortho) (b : Bool) :
    (∑ u : Selection F Q t D, ∏ v : t.Vertex, vertexAt F Q t a D H L X k b u v) =
      ∑ w ∈ bands F.sector.derivatives H, scalar b (Arboreal.factorization Q.port (rawTree t)
        (rawTree t).zones (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w (rawCaps t D)) *
        L (out F H k b (Q.port.loaded w H)) := by
  rw [changeFramesAt]
  calc
    _ = ∑ pair : Band F H × Intermediate F t D,
      L (rawActor F Q H k b pair.1) * rawProduct F Q t a D H X k b (modeTuple F t D H pair.1 pair.2) :=
      (Fintype.sum_equiv (rootChoices t (fun v => Band F (cap t D H v))).symm _ _ (fun _ => rfl)).symm
    _ = ∑ w : Band F H, L (rawActor F Q H k b w) *
        scalar b (Arboreal.factorization Q.port (rawTree t) (rawTree t).zones
          (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w.1 (rawCaps t D)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro w _
      change (∑ j : Intermediate F t D, L (rawActor F Q H k b w) *
        rawProduct F Q t a D H X k b (modeTuple F t D H w j)) = _
      rw [← Finset.mul_sum, castSum]
    _ = ∑ w ∈ bands F.sector.derivatives H, L (out F H k b (Q.port.loaded w H)) *
        scalar b (Arboreal.factorization Q.port (rawTree t) (rawTree t).zones
          (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w (rawCaps t D)) :=
      Finset.sum_coe_sort _ (fun w => L (out F H k b (Q.port.loaded w H)) *
        scalar b (Arboreal.factorization Q.port (rawTree t) (rawTree t).zones
          (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w (rawCaps t D)))
    _ = _ := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The fixed-rotation, fixed-reality contraction of every physical row is
the grade-m projection of the original finite signed tree factorization. -/
theorem factorization (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (c : Q.channels m) (X : Node t → E4) (k : Ortho) (b : Bool) :
    (∑ u : Selection F Q t D, ∏ v : t.Vertex, vertex F Q t a D m c X k b u v) =
      ∑ w ∈ bands F.sector.derivatives m, scalar b (Arboreal.factorization Q.port (rawTree t)
        (rawTree t).zones (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w (rawCaps t D)) *
        read F Q m m c (out F m k b (Q.port.loaded w m)) := by
  simpa only [WilsonSharpPhysicalTreeContractionFusion.selected] using
    factorizationAt F Q t a D m (read F Q m m c) X k b

/-- Reconstruct the complete retained root field from the physical root
channels. Every lower grade is kept at the root and at every inner edge. -/
theorem fieldFactorization (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (H : ℕ)
    (X : Node t → E4) (k : Ortho) (b : Bool) :
    (∑ q : Menu.Cut Q H, (∑ u : Selection F Q t D, ∏ v : t.Vertex,
        vertexAt F Q t a D H (read F Q q.1 H q.2) X k b u v) • physicalActor F Q H q) =
      out F H k b (∑ w ∈ bands F.sector.derivatives H, Arboreal.factorization Q.port (rawTree t)
        (rawTree t).zones (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w (rawCaps t D) • Q.port.loaded w H) := by
  let B := out F H k b (∑ w ∈ bands F.sector.derivatives H, Arboreal.factorization Q.port (rawTree t)
    (rawTree t).zones (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w (rawCaps t D) • Q.port.loaded w H)
  have one (q : Menu.Cut Q H) :
      (∑ u : Selection F Q t D, ∏ v : t.Vertex, vertexAt F Q t a D H (read F Q q.1 H q.2) X k b u v) =
        read F Q q.1 H q.2 B := by
    rw [factorizationAt]
    dsimp only [B]
    rw [add_smul, map_sum]
    simp only [map_smul, smul_eq_mul]
  calc
    _ = ∑ q : Menu.Cut Q H, read F Q q.1 H q.2 B • physicalActor F Q H q :=
      Finset.sum_congr rfl (fun q _ => congrArg (· • physicalActor F Q H q) (one q))
    _ = _ := physicalFrame F Q H B

theorem terminalFactorization (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (c : Q.channels m) (X : Node t → E4) (k : Ortho) (b : Bool) :
    (∑ u : Selection F Q t D, ∏ v : t.Vertex, vertex F Q t a D m c X k b u v) =
      ∑ w ∈ (bands F.sector.derivatives m).filter (fun w => w.1 = m),
        scalar b (Arboreal.factorization Q.port (rawTree t) (rawTree t).zones
          (Ortho.move k⁻¹ ∘ X) (leafNames F t a k b) w (rawCaps t D)) *
          read F Q m m c (out F m k b (Q.port.loaded w m)) := by
  rw [factorization]
  symm
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro w hw missing
  have low : w.1 < m := lt_of_le_of_ne ((full_bands ..).mp hw)
    (fun e => missing (Finset.mem_filter.mpr ⟨hw,e⟩))
  rw [lower F Q c w low k b, mul_zero]

end YM.Integration.WilsonSharpPhysicalTreeContractionFlat

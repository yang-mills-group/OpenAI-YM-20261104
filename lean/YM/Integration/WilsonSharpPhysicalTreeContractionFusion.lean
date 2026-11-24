import YM.Integration.WilsonSharpPhysicalTreeContractionRows
import YM.Integration.WilsonSharpPhysicalTreeContractionLayout
import YM.Integration.WilsonCenteredNestedRaised

/-! Change from the complete physical frames to the original raw modes on
the actual child sets of a finite public fusion tree, before averaging. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeContractionFusion
open Function Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedTerminalOrbit
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRealOrbit
open WilsonSharpPhysicalTreeContractionRows WilsonSharpPhysicalTreeContractionLayout
open WilsonSharpPhysicalTreeGeometry YangMills.Hierarchy
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (t : FusionTree)

abbrev Selection (D : Fin t.branches → ℕ) := (i : Fin t.branches) → Menu.Cut Q (D i)

def cap (D : Fin t.branches → ℕ) (m : ℕ) : t.Vertex → ℕ := Fin.cases m D

abbrev Modes (D : Fin t.branches → ℕ) (m : ℕ) := (v : t.Vertex) → Band F (cap t D m v)

def channel (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m) (u : Selection F Q t D) :
    t.Vertex → Σ n, Q.channels n :=
  Fin.cases ⟨m,c⟩ (fun i => ⟨(u i).1,(u i).2⟩)

def points (X : Node t → E4) (v : t.Vertex) (s : t.Child v) : E4 := X (childNode t s.1)

theorem publicPoints (x : Fin t.leaves → E4) (z : t.Vertex → E4) (v : t.Vertex) :
    points t (Sum.elim z x) v = t.positions (v := v) x z := by
  funext p
  obtain ⟨s, hs⟩ := p
  cases s <;> rfl

def seatGrade (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) : Slot t → ℕ :=
  Sum.elim (fun i => (a i).1) D

abbrev Seats (D : Fin t.branches → ℕ) := Options t (fun i => Menu.Cut Q (D i))

def tag (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) :
    (s : Slot t) → Seats F Q t D s → S.Tag
  | .inl i, _ => a i
  | .inr _, q => ⟨q.1, Q.actor q.1 q.2⟩

def resident (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) :
    (s : Slot t) → Seats F Q t D s → S.Field (seatGrade t a D s)
  | .inl i, _ => (a i).2
  | .inr i, q => physicalActor F Q (D i) q

def childTags (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ)
    (u : Selection F Q t D) (v : t.Vertex) (p : t.Child v) : S.Tag :=
  tag F Q t a D p.1 (slotChoice u p.1)

theorem publicTags (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ)
    (u : Selection F Q t D) (v : t.Vertex) :
    childTags F Q t a D u v =
      fun p : t.Child v => Sum.elim a (fun i : Fin t.branches => (⟨(u i).1, Q.actor (u i).1 (u i).2⟩ : S.Tag)) p.1 := by
  funext p
  obtain ⟨s, hs⟩ := p
  cases s <;> rfl

theorem fits (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ)
    (s : Slot t) (q : Seats F Q t D s) : (tag F Q t a D s q).1 ≤ seatGrade t a D s := by
  cases s with
  | inl i => exact le_rfl
  | inr i => exact Nat.le_of_lt_succ q.1.isLt

theorem resident_rise (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ)
    (s : Slot t) (q : Seats F Q t D s) :
    F.sector.derivatives.rise (fits F Q t a D s q) (tag F Q t a D s q).2 =
      resident F Q t a D s q := by
  cases s with
  | inl i => exact F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts _
  | inr i => rfl

def rawResident (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (k : Ortho) (b : Bool) (w : Modes F t D m) : (s : Slot t) → S.Field (seatGrade t a D s)
  | .inl i => (a i).2
  | .inr i => rawActor F Q (D i) k b (w i.succ)

def weight (D : Fin t.branches → ℕ) (m : ℕ) (k : Ortho) (b : Bool) (w : Modes F t D m) :
    (s : Slot t) → Seats F Q t D s → ℂ
  | .inl _, _ => 1
  | .inr i, q => read F Q q.1 (D i) q.2 (rawActor F Q (D i) k b (w i.succ))

theorem replaceSeat (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (k : Ortho) (b : Bool) (w : Modes F t D m) (s : Slot t) :
    ∑ q : Seats F Q t D s, weight F Q t D m k b w s q • resident F Q t a D s q =
      rawResident F Q t a D m k b w s := by
  cases s with
  | inl i =>
    change (∑ _ : Unit, (1 : ℂ) • (a i).2) = (a i).2
    simp
  | inr i => exact physicalFrame F Q (D i) _

def vertex (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (c : Q.channels m) (X : Node t → E4) (k : Ortho) (b : Bool)
    (u : Selection F Q t D) (v : t.Vertex) : ℂ :=
  read F Q (channel F Q t D m c u v).1 (cap t D m v) (channel F Q t D m c u v).2
    (restored F Q.port (cap t D m v) (points t X v) (voices (childTags F Q t a D u v)) (X (.inl v)) k b)

def project (D : Fin t.branches → ℕ) (H : ℕ) (L : S.Field H →ₗ[ℂ] ℂ) (u : Selection F Q t D) :
    (v : t.Vertex) → S.Field (cap t D H v) →ₗ[ℂ] ℂ :=
  Fin.cases L (fun i => read F Q (u i).1 (D i) (u i).2)

def vertexAt (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (H : ℕ)
    (L : S.Field H →ₗ[ℂ] ℂ) (X : Node t → E4) (k : Ortho) (b : Bool)
    (u : Selection F Q t D) (v : t.Vertex) : ℂ :=
  project F Q t D H L u v
    (restored F Q.port (cap t D H v) (points t X v) (voices (childTags F Q t a D u v)) (X (.inl v)) k b)

theorem selected (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (c : Q.channels m) (X : Node t → E4) (k : Ortho) (b : Bool)
    (u : Selection F Q t D) (v : t.Vertex) :
    vertexAt F Q t a D m (read F Q m m c) X k b u v = vertex F Q t a D m c X k b u v :=
  Fin.cases rfl (fun _ => rfl) v

def output (D : Fin t.branches → ℕ) (H : ℕ) (L : S.Field H →ₗ[ℂ] ℂ) (k : Ortho) (b : Bool)
    (u : Selection F Q t D) (v : t.Vertex) (w : Band F (cap t D H v)) : ℂ :=
  project F Q t D H L u v (rawActor F Q (cap t D H v) k b w)

def localRow (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ)
    (X : Node t → E4) (k : Ortho) (b : Bool) (v : t.Vertex) (w : Mode F.sector.derivatives) :
    MultilinearMap ℂ (fun p : t.Child v => S.Field (seatGrade t a D p.1)) ℂ :=
  modeRow F Q w (points t X v) (X (.inl v)) k b

theorem vertexFrame (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (H : ℕ)
    (L : S.Field H →ₗ[ℂ] ℂ) (X : Node t → E4) (k : Ortho) (b : Bool)
    (u : Selection F Q t D) (v : t.Vertex) :
    vertexAt F Q t a D H L X k b u v =
      ∑ w : Band F (cap t D H v), localRow F Q t a D X k b v w.1
        (fun p => resident F Q t a D p.1 (slotChoice u p.1)) * output F Q t D H L k b u v w := by
  let r := childTags F Q t a D u v
  have p : degrees r ≤ fun j : t.Child v => seatGrade t a D j.1 :=
    fun j => fits F Q t a D j.1 (slotChoice u j.1)
  have inc : (fun j => F.sector.derivatives.rise (p j) (voices r j)) =
      (fun j : t.Child v => resident F Q t a D j.1 (slotChoice u j.1)) :=
    funext fun j => resident_rise F Q t a D j.1 (slotChoice u j.1)
  have h := WilsonCenteredNestedRaised.original F Q p (cap t D H v)
    (points t X v) (voices r) (X (.inl v)) k b
  rw [inc] at h
  unfold vertexAt
  change project F Q t D H L u v (restored F Q.port _ _ (voices r) _ _ _) = _
  rw [← h, ← rawFrame F Q, map_sum]
  simp only [map_smul, smul_eq_mul, localRow, output]

def rootWeight (m : ℕ) (c : Q.channels m) (k : Ortho) (b : Bool) (w : Band F m) : ℂ :=
  read F Q m m c (rawActor F Q m k b w)

def rawProduct (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (X : Node t → E4) (k : Ortho) (b : Bool) (w : Modes F t D m) : ℂ :=
  ∏ v : t.Vertex, localRow F Q t a D X k b v (w v).1
    (fun p => rawResident F Q t a D m k b w p.1)

private theorem weight_slot (D : Fin t.branches → ℕ) (m : ℕ) (k : Ortho) (b : Bool)
    (w : Modes F t D m) (u : Selection F Q t D) (s : Slot t) :
    weight F Q t D m k b w s (slotChoice u s) =
      Sum.elim (fun _ : Fin t.leaves => 1) (fun i => weight F Q t D m k b w (.inr i) (u i)) s := by
  cases s <;> rfl

private theorem allWeights (D : Fin t.branches → ℕ) (H : ℕ) (L : S.Field H →ₗ[ℂ] ℂ)
    (k : Ortho) (b : Bool) (w : Modes F t D H) (u : Selection F Q t D) :
    (∏ v : t.Vertex, output F Q t D H L k b u v (w v)) =
      L (rawActor F Q H k b (w 0)) *
        ∏ v : t.Vertex, ∏ p : t.Child v, weight F Q t D H k b w p.1 (slotChoice u p.1) := by
  have h : (∏ v : t.Vertex, ∏ p : t.Child v, weight F Q t D H k b w p.1 (slotChoice u p.1)) =
      ∏ v : t.Vertex, ∏ p : t.Child v, Sum.elim (fun _ : Fin t.leaves => 1)
        (fun i => weight F Q t D H k b w (.inr i) (u i)) p.1 :=
    Finset.prod_congr rfl (fun v _ => Finset.prod_congr rfl (fun p _ => weight_slot F Q t D H k b w u p.1))
  rw [h, collect, Fin.prod_univ_succ]
  rfl

private theorem fixedModes (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (X : Node t → E4) (k : Ortho) (b : Bool) (w : Modes F t D m) :
    (∑ u : Selection F Q t D, ∏ v : t.Vertex,
        (∏ p : t.Child v, weight F Q t D m k b w p.1 (slotChoice u p.1)) *
          localRow F Q t a D X k b v (w v).1 (fun p => resident F Q t a D p.1 (slotChoice u p.1))) =
      rawProduct F Q t a D m X k b w := by
  let R (v : t.Vertex) (q : (p : t.Child v) → Seats F Q t D p.1) :=
    (∏ p : t.Child v, weight F Q t D m k b w p.1 (q p)) *
      localRow F Q t a D X k b v (w v).1 (fun p => resident F Q t a D p.1 (q p))
  change (∑ u : Selection F Q t D, ∏ v : t.Vertex, R v (fun p => slotChoice u p.1)) = _
  rw [distribute t (fun i => Menu.Cut Q (D i)) R]
  unfold rawProduct
  apply Finset.prod_congr rfl
  intro v _
  symm
  let M := localRow F Q t a D X k b v (w v).1
  have eq : (fun p : t.Child v => rawResident F Q t a D m k b w p.1) =
      (fun p : t.Child v => ∑ q : Seats F Q t D p.1,
        weight F Q t D m k b w p.1 q • resident F Q t a D p.1 q) :=
    funext fun p => (replaceSeat F Q t a D m k b w p.1).symm
  change M _ = _
  rw [eq, M.map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact M.map_smul_univ (fun p => weight F Q t D m k b w p.1 (q p))
    (fun p => resident F Q t a D p.1 (q p))

theorem changeFramesAt (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (H : ℕ)
    (L : S.Field H →ₗ[ℂ] ℂ) (X : Node t → E4) (k : Ortho) (b : Bool) :
    (∑ u : Selection F Q t D, ∏ v : t.Vertex, vertexAt F Q t a D H L X k b u v) =
      ∑ w : Modes F t D H, L (rawActor F Q H k b (w 0)) * rawProduct F Q t a D H X k b w := by
  simp_rw [vertexFrame, Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← fixedModes, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.prod_mul_distrib, allWeights, Finset.prod_mul_distrib]
  ring

theorem changeFrames (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ) (m : ℕ)
    (c : Q.channels m) (X : Node t → E4) (k : Ortho) (b : Bool) :
    (∑ u : Selection F Q t D, ∏ v : t.Vertex, vertex F Q t a D m c X k b u v) =
      ∑ w : Modes F t D m, rootWeight F Q m c k b (w 0) * rawProduct F Q t a D m X k b w := by
  simpa only [selected, rootWeight] using changeFramesAt F Q t a D m (read F Q m m c) X k b

end YM.Integration.WilsonSharpPhysicalTreeContractionFusion

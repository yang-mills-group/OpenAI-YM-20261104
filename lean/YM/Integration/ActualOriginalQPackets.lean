import YM.Integration.ActualOriginalQReaders
import YM.Integration.NativeFinitePacketLaws
import YM.Integration.NativeFinitePacketPayment

/-! A literal finite packet for every coefficient of the same full-Q column.
The marker/test type is unchanged; Glyph choices only enlarge the finite row
index. Every row keeps both its original field footprint and the complete
native reader stub. Payment uses the actual finite cost and cover maximum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQPackets

open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM
open ActualOriginalQReaders
open MergeProof.Accent
open FVA1
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B)
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

abbrev degree (s : Slot u) : ℕ := s.2.size

def plot (i : V) : Support (R.family.side L p) :=
  (ActualRunQlocalNativeTuple.positions D).stub i ∪
    (Finset.univ : Finset (MS.Menus.Glyph B (u i).h)).biUnion
      (fun g => (R.family.localSection g.size).footprint
        (ActualRunQlocalNativeTuple.root D i))

def positions : Positions V (R.family.side L p) where
  origin := ActualRunQlocalNativeTuple.root D
  stub := plot D u
  mem i := Finset.mem_union_left _ ((ActualRunQlocalNativeTuple.positions D).mem i)

omit [DecidableEq V] [Fintype V] in
private theorem original_subset (i : V) :
    (ActualRunQlocalNativeTuple.positions D).stub i ⊆ plot D u i :=
  Finset.subset_union_left

omit [DecidableEq V] [Fintype V] in
private theorem section_subset (s : Slot u) :
    (R.family.localSection s.2.size).footprint (ActualRunQlocalNativeTuple.root D s.1)
      ⊆ plot D u s.1 := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s.2, Finset.mem_univ _, hx⟩)

abbrev Row := ActualRunKernelPackets.Index R (degree u)

abbrev baseToken (N : ℕ) (s : Row (R := R) u) :=
  ActualRunKernelPackets.term R (ActualRunQlocalNativeTuple.orbit D) (degree u)
    N p L (fun t => ActualRunQlocalNativeTuple.root D t.1)
    (labels Q D u μ orders N) (coefficientBudget Q D u μ orders N) s

def token (N : ℕ) (s : Row (R := R) u) :
    Token G (R.family.side L p) (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood)
      (ActualRunKernelPackets.tokenRank R (degree u) s) :=
  { baseToken Q D u μ orders N s with plot := plot D u s.1.1 }

def packets (N : ℕ) :
    MarkedPackets (ActualRunQlocalNativeTuple.orbit D) G (R.family.side L p)
      (Stock.census V) :=
  let e := (Fintype.equivFin (Row (R := R) u)).symm
  MarkedPackets.ofFin
    (fun k => (Stock.census V).fire (e k).1.1)
    (fun k => ActualRunKernelPackets.tokenRank R (degree u) (e k))
    (fun k => -(ActualRunKernelPackets.fieldRank R (degree u) (e k) : ℤ))
    (fun k => token Q D u μ orders N (e k))
    (fun k => (Stock.census V).fire_hot (e k).1.1)
    (fun k => by
      have h := ActualRunKernelPackets.term_grade R (degree u) (e k)
      omega)

def packetCount : ℕ := Fintype.card (Row (R := R) u)

def packetCost (N : ℕ) (w : V → ℝ) (width : ℝ) : ℝ :=
  NativeFinitePacketPayment.totalCost (packets Q D u μ orders N)
    (packetCount (R := R) u) w (Pert.Asymptotics.regulatorRun R.family N p L) width

def packetCover (N : ℕ) (P : BudgetPoint) : ℕ :=
  NativeFinitePacketPayment.coverOffset (packets Q D u μ orders N)
    (packetCount (R := R) u) P

omit [DecidableEq V] [Fintype V] in
private theorem token_bound (N : ℕ) (s : Row (R := R) u)
    (x : IndependentTests (ActualRunQlocalNativeTuple.orbit D)) :
    (∑ j, ‖(token Q D u μ orders N s).gem j
      (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)‖) ≤
        (token Q D u μ orders N s).coin := by
  exact ActualRunKernelPackets.term_bound R
    (ActualRunQlocalNativeTuple.orbit D) (degree u) N p L
    (fun t => ActualRunQlocalNativeTuple.root D t.1)
    (labels Q D u μ orders N) (coefficientBudget Q D u μ orders N) s
    (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)
    (coordinate_bound Q D u μ orders N s.1 s.2.1 x)

omit [DecidableEq V] [Fintype V] in
private theorem token_reads (N : ℕ) (s : Row (R := R) u)
    (j : Fin (ActualRunKernelPackets.tokenRank R (degree u) s) → G.ColorIndex) :
    Comparison.Density.Testing.Reads (ActualRunQlocalNativeTuple.readerRegion D)
      (token Q D u μ orders N s).plot {s.1.1}
      ((token Q D u μ orders N s).gem j) := by
  intro x y h
  have hr := coordinate_reads Q D u μ orders N s.1 s.2.1
    (plot D u s.1.1) (original_subset D u s.1.1) x y h
  let a : ℂ := NativeCurvatureTensor.coefficient (G := G)
    (fun k => (NativeCurvatureTensor.word s.2.2.val k).2) j
  let b : ℂ := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
    ActualRunKernelPackets.fieldRank R (degree u) s *
      ActualRunKernelPackets.weight R (degree u) N p L s
  change a * (b * labels Q D u μ orders N s.1 x s.2.1) =
    a * (b * labels Q D u μ orders N s.1 y s.2.1)
  exact congrArg (fun z : ℂ => a * (b * z)) hr

omit [Fintype V] in
private theorem token_letter (N : ℕ) (s : Row (R := R) u)
    (j : Fin (ActualRunKernelPackets.tokenRank R (degree u) s) → G.ColorIndex) :
    RG3.Held.Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood)
      {s.1.1} ((token Q D u μ orders N s).gem j) := by
  let a : ℂ := NativeCurvatureTensor.coefficient (G := G)
    (fun k => (NativeCurvatureTensor.word s.2.2.val k).2) j
  let b : ℂ := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
    ActualRunKernelPackets.fieldRank R (degree u) s *
      ActualRunKernelPackets.weight R (degree u) N p L s
  change RG3.Held.Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood)
    {s.1.1} (fun x => a * (b * labels Q D u μ orders N s.1 x s.2.1))
  exact ((coordinate_letter Q D u μ orders N s.1 s.2.1).cmul b).cmul a

private structure Certificate (m : (Stock.census V).Mode) {q : ℕ}
    (T : Token G (R.family.side L p)
      (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood) q) : Prop where
  coefficient : 0 ≤ T.coin ∧
    ∀ x : IndependentTests (ActualRunQlocalNativeTuple.orbit D),
      (∑ j, ‖T.gem j (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)‖) ≤ T.coin
  paths : ∀ x : TestSpace (ActualRunQlocalNativeTuple.orbit D),
    (T.re x).length ≤ T.fall ∧ (T.re x).footprint T.root ⊆ T.plot
  addresses : ∀ i ∈ m.val, (positions D u).stub i ⊆ T.plot
  symmetry : ∀ x U (k : G.El),
    T.touch x (fun i => G.adjoint k (U i)) = T.touch x U
  reads : ∀ j, Comparison.Density.Testing.Reads
    (ActualRunQlocalNativeTuple.readerRegion D) T.plot m.val (T.gem j)
  letter : ∀ j, RG3.Held.Letter ℂ
    (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood) m.val (T.gem j)

private theorem token_certificate (N : ℕ) (s : Row (R := R) u) :
    Certificate D u ((Stock.census V).fire s.1.1) (token Q D u μ orders N s) := by
  refine ⟨⟨?_, token_bound Q D u μ orders N s⟩, ?_, ?_, ?_,
    token_reads Q D u μ orders N s, token_letter Q D u μ orders N s⟩
  · let x : IndependentTests (ActualRunQlocalNativeTuple.orbit D) := fun i =>
      ⟨0, (Orbit.Bill.zero (U := ActualRunQlocalNativeTuple.orbit D i)).more zero_le_one⟩
    exact (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans
      (token_bound Q D u μ orders N s x)
  · intro x
    refine ⟨le_rfl, ?_⟩
    exact (ActualRunKernelPackets.term_footprint R (ActualRunQlocalNativeTuple.orbit D)
      (degree u) N p L (fun t => ActualRunQlocalNativeTuple.root D t.1)
      (labels Q D u μ orders N) (coefficientBudget Q D u μ orders N) s).trans
        (section_subset D u s.1)
  · intro i hi
    have he : i = s.1.1 := Finset.mem_singleton.mp hi
    subst i
    exact le_rfl
  · intro x U k
    change (baseToken Q D u μ orders N s).touch x (fun i => G.adjoint k (U i)) =
      (baseToken Q D u μ orders N s).touch x U
    simp only [baseToken, ActualRunKernelPackets.term,
      NativeCurvatureTensor.token_touch, NativeCurvatureTensor.value_invariant]

private theorem certificates (N : ℕ) (i : ℕ)
    (T : Token G (R.family.side L p)
      (fun j => (ActualRunQlocalNativeTuple.orbit D j).Mood)
      ((packets Q D u μ orders N).rank i))
    (hT : (packets Q D u μ orders N).packet i = some T) :
    Certificate D u ((packets Q D u μ orders N).mode i) T := by
  unfold packets at hT ⊢
  exact MarkedPackets.ofFin_all _ _ _ _ _ _
    (fun m _ _ t => Certificate D u m t)
    (fun _ => token_certificate Q D u μ orders N _) i T hT

/-- The actual finite cost is paid without adding a price premise or dropping a row. -/
theorem packets_paid (N : ℕ) (P : BudgetPoint) (w : V → ℝ) (width : ℝ)
    (hwidth : 0 < width) (hw : ∀ i, 0 < w i) :
    (packets Q D u μ orders N).Paid P (positions D u).stub
      (ActualRunQlocalNativeTuple.readerRegion D) w
      (Pert.Asymptotics.regulatorRun R.family N p L) width
      (packetCost Q D u μ orders N w width) (packetCover Q D u μ orders N P) 0 := by
  have hf : ∀ i, packetCount (R := R) u ≤ i →
      (packets Q D u μ orders N).packet i = none := by
    intro i hi
    unfold packets
    exact MarkedPackets.ofFin_absent _ _ _ _ _ _ i hi
  exact NativeFinitePacketPayment.paid (packets Q D u μ orders N)
    (packetCount (R := R) u) w (Pert.Asymptotics.regulatorRun R.family N p L) width P hf
    (positions D u).stub (ActualRunQlocalNativeTuple.readerRegion D) hwidth hw
    (fun i T hT => (certificates Q D u μ orders N i T hT).coefficient)
    (fun i T hT => (certificates Q D u μ orders N i T hT).paths)
    (fun i T hT => (certificates Q D u μ orders N i T hT).addresses)
    (fun i T hT => (certificates Q D u μ orders N i T hT).symmetry)
    (fun i T hT => (certificates Q D u μ orders N i T hT).reads)
    (fun i T hT => (certificates Q D u μ orders N i T hT).letter)

private theorem send_sum {I : Type} [Fintype I]
    (m : (Stock.census V).Mode) (f : I → ℂ) :
    Poly.send m (∑ i, f i) = ∑ i, Poly.send m (f i) := by
  ext s
  simp only [Poly.part_send, Poly.part_sum]
  by_cases h : s = m <;> simp [h]

/-- Full original-field polynomial at the actual regulator, before Poly.pass. -/
theorem packets_read (N : ℕ) (hL : L ≤ N)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    (packets Q D u μ orders N).read x (Pert.Asymptotics.regulatorRun R.family N p L) U =
      Mach (Stock.census V) (fun i =>
        ActualRunQlocalNativeTuple.reader D i (x i) *
          ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
            (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i)) := by
  let P₀ := ActualRunKernelPackets.packets R (Stock.census V)
    (ActualRunQlocalNativeTuple.orbit D) (degree u) N p L
    (fun s => ActualRunQlocalNativeTuple.root D s.1)
    (labels Q D u μ orders N) (coefficientBudget Q D u μ orders N)
    (fun s => (Stock.census V).fire s.1) (fun s => (Stock.census V).fire_hot s.1)
  have he : (packets Q D u μ orders N).read x
      (Pert.Asymptotics.regulatorRun R.family N p L) U =
      P₀.read x (Pert.Asymptotics.regulatorRun R.family N p L) U := by
    dsimp only [packets, P₀, ActualRunKernelPackets.packets]
    rw [MarkedPackets.ofFin_read, MarkedPackets.ofFin_read]
    rfl
  rw [he, ActualRunKernelPackets.packets_read (hL := hL), Fintype.sum_sigma]
  unfold Mach
  apply Finset.sum_congr rfl
  intro i _
  exact (send_sum ((Stock.census V).fire i)
    (fun g : MS.Menus.Glyph B (u i).h =>
      ActualRunPhysicalPages.kernel R N p L g.size
        (labels Q D u μ orders N ⟨i, g⟩ x)
        (ActualRunQlocalNativeTuple.root D i) U)).symm.trans
    (congrArg (Poly.send ((Stock.census V).fire i))
      (column_read Q D u μ orders N i x U))

/-- The full normalized source factor uses the same packet and all its modes. -/
theorem source_factor (N : ℕ) (hL : L ≤ N)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    Poly.pass ((packets Q D u μ orders N).read x
      (Pert.Asymptotics.regulatorRun R.family N p L) U) =
      Poly.pass (Mach (Stock.census V) (fun i =>
        ActualRunQlocalNativeTuple.reader D i (x i) *
          ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
            (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i))) := by
  rw [packets_read Q D u μ orders N hL x U]

end YM.Integration.ActualOriginalQPackets
end

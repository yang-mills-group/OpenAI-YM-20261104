import YM.Integration.ActualOriginalQPackets
import YM.Integration.QlocalPageAggregation
import YM.Integration.ActualRunQlocalTuplePrepared

/-! The complete finite Q coefficient columns as an actual all-test Taste.
The original representation, original native readers and full Glyph list
are fixed before the input is constructed. Every original forced gas row
survives the Page aggregation. Analytic colors and admission are separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQInput
open Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open MergeProof MergeProof.Accent MergeProof.Replicums
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses
open ActualOriginalQReaders
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type}
  [DecidableEq V] [Fintype V] [Nonempty V]
  (Q : MS.Land.Prescription B)
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

def atomPositions : Positions (Slot u) (R.family.side L p) where
  origin s := ActualRunQlocalNativeTuple.root D s.1
  stub s := (ActualOriginalQPackets.positions D u).stub s.1
  mem s := (ActualOriginalQPackets.positions D u).mem s.1

abbrev atomPages (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :=
  ActualRunFullPages.pages R hG N p L hL (atomPositions D u)
    (ActualOriginalQPackets.degree u)
    (scaledCoordinates (R := R) (p := p) (L := L) u N)

def pages (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    ActualRunFullPages.Index (atomPositions D u) →
      Page (Stock.census V) (R.family.path.rep N p L) :=
  fun j => QlocalPageAggregation.page (fun s : Slot u => s.1) (atomPages D u hG N hL j)

def coefficient (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (j : ActualRunFullPages.Index (atomPositions D u))
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) : ℂ :=
  QlocalPageAggregation.weight (fun s : Slot u => s.1)
    (fun s => readers Q D u μ orders s (x s.1)) (atomPages D u hG N hL j).s

def input (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    Taste (TestSpace (ActualRunQlocalNativeTuple.orbit D))
      (ActualOriginalQPackets.positions D u).origin
      (R.family.path.rep N p L) (Stock.census V) :=
  QlocalFinitePageTaste.presentation (pages D u hG N hL)
    (ActualOriginalQPackets.positions D u) (coefficient Q D u μ orders hG N hL)

omit [Nonempty V] in
private theorem page_stubs (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (j : ActualRunFullPages.Index (atomPositions D u)) :
    ∀ i ∈ (pages D u hG N hL j).s.val,
      (ActualOriginalQPackets.positions D u).stub i ⊆
        Seal.scope (R.family.path.rep N p L) (pages D u hG N hL j).shellx := by
  have hs : ∀ s ∈ (atomPages D u hG N hL j).s.val,
      (atomPositions D u).stub s ⊆
        Seal.scope (R.family.path.rep N p L) (atomPages D u hG N hL j).shellx := by
    rcases j with j | j
    · intro s hs
      have he : s = j := Finset.mem_singleton.mp hs
      subst s
      exact Finset.subset_union_right
    · intro s hs
      have hk := congrArg Prod.fst (cardK (actual_keeper R hG N L p hL) j.1)
      change (atomPositions D u).stub s ⊆
        ((R.family.path.rep N p L).activities.forced
          (cart (actual_keeper R hG N L p hL) j.1)).support
      change ((R.family.path.rep N p L).activities.forced
        (cart (actual_keeper R hG N L p hL) j.1)).support = j.1.val.1 at hk
      rw [hk]
      exact j.2.property.2 s hs
  intro i hi
  change i ∈ (atomPages D u hG N hL j).s.val.image (fun s : Slot u => s.1) at hi
  rcases Finset.mem_image.mp hi with ⟨s, hs', rfl⟩
  exact hs s hs'

omit [Fintype V] [Nonempty V] in
private theorem coordinate_letter (s : Slot u) :
    Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood) {s.1}
      (fun x => readers Q D u μ orders s (x s.1)) := by
  constructor
  · intro x y h
    exact congrArg (readers Q D u μ orders s)
      (h s.1 (Finset.mem_singleton_self s.1))
  · intro x i hi a b
    have he : i = s.1 := Finset.mem_singleton.mp hi
    subst i
    simp
  · intro x i hi a b
    have he : i = s.1 := Finset.mem_singleton.mp hi
    subst i
    simp

omit [Fintype V] [Nonempty V] in
private theorem product_letter (s : Finset (Slot u))
    (hs : Set.InjOn (fun a : Slot u => a.1) (s : Set (Slot u))) :
    Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood)
      (s.image (fun a => a.1))
      (fun x => ∏ a ∈ s, readers Q D u μ orders a (x a.1)) := by
  revert hs
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    simpa using (Letter.const (K := ℂ)
      (T := fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood) (1 : ℂ))
  | @insert a s ha ih =>
    intro hs
    have hu : a.1 ∉ s.image (fun b => b.1) := by
      intro h
      rcases Finset.mem_image.mp h with ⟨b, hb, he⟩
      have hba : b = a :=
        hs (Finset.mem_insert_of_mem hb) (Finset.mem_insert_self a s) he
      exact ha (hba ▸ hb)
    have hsmall := hs.mono (Finset.coe_subset.mpr (Finset.subset_insert a s))
    have hd : Disjoint ({a.1} : Finset V) (s.image (fun b => b.1)) := by
      simpa using hu
    have h := (coordinate_letter Q D u μ orders a).bind (ih hsmall) hd
    have hindex : (insert a s).image (fun b : Slot u => b.1) =
        ({a.1} : Finset V) ∪ s.image (fun b => b.1) := by
      rw [Finset.image_insert, Finset.singleton_union]
    have hfun :
        (fun x : TestSpace (ActualRunQlocalNativeTuple.orbit D) =>
          ∏ b ∈ insert a s, readers Q D u μ orders b (x b.1)) =
        ((fun x => readers Q D u μ orders a (x a.1)) *
          fun x => ∏ b ∈ s, readers Q D u μ orders b (x b.1)) := by
      funext x
      exact Finset.prod_insert ha
    exact Eq.mpr
      (congrArg₂ (fun (t : Finset V)
        (f : TestSpace (ActualRunQlocalNativeTuple.orbit D) → ℂ) =>
          Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood) t f)
        hindex hfun) h

omit [Nonempty V] in
private theorem coefficient_letter (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (j : ActualRunFullPages.Index (atomPositions D u)) :
    Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood)
      (pages D u hG N hL j).s.val (coefficient Q D u μ orders hG N hL j) := by
  change Letter ℂ (fun i => (ActualRunQlocalNativeTuple.orbit D i).Mood)
    ((atomPages D u hG N hL j).s.val.image (fun s : Slot u => s.1))
    (fun x => if Set.InjOn (fun s : Slot u => s.1)
      ((atomPages D u hG N hL j).s.val : Set (Slot u))
      then ∏ s ∈ (atomPages D u hG N hL j).s.val,
        readers Q D u μ orders s (x s.1) else 0)
  split_ifs with h
  · exact product_letter Q D u μ orders _ h
  · exact Letter.still

/-- One fixed zero-test layout retains the complete original vacuum gas. -/
theorem active_zero (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    ((input Q D u μ orders hG N hL).leaf
      (fun i => (0 : (ActualRunQlocalNativeTuple.orbit D i).Mood))).Active := by
  apply QlocalFinitePageTaste.active_zero
  intro j
  unfold coefficient QlocalPageAggregation.weight
  split_ifs
  · obtain ⟨s, hs⟩ := (atomPages D u hG N hL j).marked
    exact Finset.prod_eq_zero hs (map_zero (readers Q D u μ orders s))
  · rfl

/-- Every retained Page uses each original independent marker at most once. -/
theorem multilinear (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    LocalComparison.Multilinear (ActualRunQlocalNativeTuple.orbit D)
      (input Q D u μ orders hG N hL) := by
  apply QlocalFinitePageTaste.multilinear
  exact coefficient_letter Q D u μ orders hG N hL

/-- The full field footprints and original native reader stubs are retained. -/
theorem retains (hG : G.Simple) (N : ℕ) (hL : L ≤ N) :
    FunctionalRetains (input Q D u μ orders hG N hL)
      (ActualOriginalQPackets.positions D u).stub :=
  QlocalFinitePageTaste.functionalRetains _ _ _ (page_stubs D u hG N hL)

omit [Nonempty V] in
private theorem aggregate_column (N : ℕ)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) (i : V)
    (U : Config G (R.family.side L p)) :
    JointSignedInitialization.Rooted.aggregate (fun s : Slot u => s.1)
      (fun s => readers Q D u μ orders s (x s.1))
      (fun s => ActualRunPhysicalPages.kernel R N p L s.2.size
        (scaledCoordinates (R := R) (p := p) (L := L) u N s)
        (ActualRunQlocalNativeTuple.root D s.1)) i U =
      ActualRunQlocalNativeTuple.reader D i (x i) *
        ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
          (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i) := by
  rw [← column_read Q D u μ orders N i x U]
  unfold JointSignedInitialization.Rooted.aggregate
  rw [Fintype.sum_sigma, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · apply Finset.sum_congr rfl
    intro g _
    change (if i = i then
      readers Q D u μ orders ⟨i, g⟩ (x i) *
        ActualRunPhysicalPages.kernel R N p L g.size
          (scaledCoordinates (R := R) (p := p) (L := L) u N ⟨i, g⟩)
          (ActualRunQlocalNativeTuple.root D i) U else 0) = _
    exact (if_pos rfl).trans ((congrArg
      (fun z : ℂ => readers Q D u μ orders ⟨i, g⟩ (x i) * z)
      (kernel_coordinates u N ⟨i, g⟩
        (ActualRunQlocalNativeTuple.root D i) U)).trans
      (kernel_label Q D u μ orders N ⟨i, g⟩ x
        (ActualRunQlocalNativeTuple.root D i) U).symm)
  · intro j _ hji
    simp only [if_neg (Ne.symm hji), Finset.sum_const_zero]

/-- The full original-Q coefficient columns, before any field integral. -/
theorem density_full (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ s : Slot u, R.family.ref s.2.size ≤ L)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    ((input Q D u μ orders hG N hL).leaf x).density U =
      birth (Stock.census V) (R.family.path.rep N p L)
        (fun i W => ActualRunQlocalNativeTuple.reader D i (x i) *
          ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
            (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) W (orders i)) U := by
  change ((QlocalFinitePageTaste.presentation (pages D u hG N hL)
    (ActualOriginalQPackets.positions D u) (coefficient Q D u μ orders hG N hL)).leaf x).density U = _
  rw [QlocalFinitePageTaste.density _ _ _ (page_stubs D u hG N hL)]
  refine (QlocalPageAggregation.actual_essence (fun s : Slot u => s.1) R hG N p L hL
    (atomPositions D u) (ActualOriginalQPackets.degree u)
    (scaledCoordinates (R := R) (p := p) (L := L) u N) href
    (fun s => readers Q D u μ orders s (x s.1)) U).trans ?_
  apply congrArg (fun f => birth (Stock.census V) (R.family.path.rep N p L) f U)
  funext i W
  exact aggregate_column Q D u μ orders N x i W

/-- Exact same-packet factorization with the original full representation. -/
theorem density_packet_factor (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ s : Slot u, R.family.ref s.2.size ≤ L)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    ((input Q D u μ orders hG N hL).leaf x).density U =
      ((R.family.path.rep N p L).eval U : ℂ) •
        Poly.pass ((ActualOriginalQPackets.packets Q D u μ orders N).read x
          (Pert.Asymptotics.regulatorRun R.family N p L) U) := by
  rw [density_full Q D u μ orders hG N hL href,
    ActualOriginalQPackets.packets_read Q D u μ orders N hL]
  rfl

/-- Structural preparation uses the same finite paid packet once its exact
analytic color convention is supplied. No admission bound is assumed here. -/
def packet_prepared (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ s : Slot u, R.family.ref s.2.size ≤ L)
    (colors : TestSpace (ActualRunQlocalNativeTuple.orbit D) →
      Comparison.RG02.Bulk.Colors (Stock.census V) G (R.family.side L p))
    (hColors : InputColors colors (ActualOriginalQPackets.packets Q D u μ orders N))
    (w cost : V → ℝ) (hw : ∀ i, 0 < w i) (hcost : ∀ i, 0 < cost i) :
    Global.Prepared N p L (ActualRunQlocalNativeTuple.packetCarrier R N p L hL)
      (ActualOriginalQPackets.positions D u).origin (input Q D u μ orders hG N hL)
      colors (ActualOriginalQPackets.packets Q D u μ orders N) w (envelopeProduct cost) 0 :=
  Global.Prepared.of_bare_factorization N p L
    (ActualRunQlocalNativeTuple.packetCarrier R N p L hL)
    (ActualOriginalQPackets.positions D u).origin (input Q D u μ orders hG N hL)
    colors (ActualOriginalQPackets.packets Q D u μ orders N) w (envelopeProduct cost)
    (fun i => (0 : (ActualRunQlocalNativeTuple.orbit D i).Mood))
    (active_zero Q D u μ orders hG N hL) hColors hw
    (fun _ => Finset.prod_pos (fun i _ => hcost i)) (by rfl)
    (ActualRunQlocalNativeTuple.packet_gas_summable R N p L hL)
    (density_packet_factor Q D u μ orders hG N hL href)

end YM.Integration.ActualOriginalQInput
end

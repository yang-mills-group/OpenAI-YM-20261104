import YM.Integration.WilsonRootedOPEPhase

/-! Actual aggregated OPE phase menus from the registered rooted sheet, with their original readers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPhysicalMenu
open Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open MergeProof MergeProof.Accent MergeProof.Replicums MergeProof.Ribbon
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open Extra.Trajectories Push.GridApprox.Nil
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
    {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
    (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
local notation "pos" => ActualOriginalQPackets.positions D u
local notation "atoms" => ActualOriginalQInput.atomPositions D u
local notation "rows" => ActualOriginalQInput.pages D u hG N hL
local notation "fees" => ActualOriginalQInput.coefficient Q D u μ orders hG N hL
local notation "fine" => R.family.path.rep N p L
local notation "index" => ActualRunFullPages.Index (atoms)
local notation "Ω" => TestSpace (ActualRunQlocalNativeTuple.orbit D)

omit [Nonempty V] in
theorem regrouped (v : (index)→ℝ) (b : ℝ)
    (physical : MenuSafe (ActualOriginalQInput.atomPages D u hG N hL) (atoms) v (fun _=>1) b) :
    MenuSafe (rows) (pos) v (fun _=>1) b := by
  refine ⟨?_,fun _=>zero_lt_one,?_⟩
  · intro j
    have e := physical.each j
    refine ⟨?_, ?_, e.closes⟩
    · intro i hi
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hi
      exact e.stubs s hs
    · intro k hk
      obtain ⟨reg, jet⟩ := e.opens k hk
      refine ⟨reg, ?_⟩
      intro i hi
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hi
      exact jet s hs
  · simpa [ActualOriginalQInput.pages,QlocalPageAggregation.page,Page.due,Poly.toll] using physical.hit

/-- The phase factor has the fixed finite number of actual original reader slots, regardless of how many gauge barcodes the period contains. -/
theorem original (v : (index)→ℝ) (b : ℝ)
    (physical : MenuSafe (ActualOriginalQInput.atomPages D u hG N hL) (atoms) v (fun _=>1) b)
    (stock : Menu.Arsenal (fine)) :
    ∃ a : (Ω) → Bool × (index) → Menu.Hat (Stock.census V) (fine), ∀ x,
      ((ActualOriginalQInput.input Q D u μ orders hG N hL).leaf x).density =
        GapsLocal.Full.given (a x) 0 ∧
      Menu.Offer (pos).origin (a x) (fun _=>1) (fine).p.B ((fine).p.supportExponent-4)
        (WilsonRootedOPEPhase.wallet (fun s : Slot u=>readers Q D u μ orders s (x s.1))*(b+b)) := by
  let w := fun _ : V=>(1:ℝ)
  have safe := regrouped D u hG N hL v b physical
  let cards := FVA1.costume (rows) (pos) v w stock safe
  let hat (x : Ω) := MenuBridge.vital cards (fun i (_ : V→Unit) => (fees) i.2 x) (fun _=>())
  refine ⟨hat, ?_⟩
  intro x
  constructor
  · funext U
    rw [show ((ActualOriginalQInput.input Q D u μ orders hG N hL).leaf x).density U = _ from
        QlocalFinitePageTaste.density (rows) (pos) (fees) (fun j=> (safe.each j).stubs) x U]
    exact congrFun (FVA1.pegs (rows) (pos) v w stock safe (R.makes.wilson.represents N p L hL).good
      (fun i (_ : V→Unit) => (fees) i x) (fun _ _ => 0) (fun _=>())) U
  obtain ⟨offered,_⟩ := FVA1.price_cards (rows) (pos) v w stock safe
  let γ := fun s : Slot u=>readers Q D u μ orders s (x s.1)
  apply WilsonRootedOPEPhase.offered cards (fun i=>(fees) i.2 x) _ _ (fun _=>zero_lt_one) _ _ _ (WilsonRootedOPEPhase.wallet γ) _ _ offered
  · exact pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _=>norm_nonneg _)) _
  · exact fun i=>WilsonRootedOPEPhase.original _ γ _

end YM.Integration.WilsonRootedOPEPhysicalMenu

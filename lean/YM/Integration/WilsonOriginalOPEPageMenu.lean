import YM.Integration.ActualOriginalQInput
import YM.Integration.QLocalPhysicalBirthMenu
import YM.Integration.QLocalFullRootedOffer

/-! The actual OPE page coefficients, including every forced old barcode, as a
finite real/imaginary charged menu on the very same original Wilson representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOPEPageMenu
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
/-- Grouping original point slots onto the same requested marker preserves its
true support, derivative bounds and exceptional eligibility, on each signed page. -/
theorem entered (href : ∀ s : Slot u, R.family.ref s.2.size ≤ L) :
    ∃ v : (index) → ℝ, ∀ j, ((rows) j).Entry (pos) (v j) := by
  let d := ActualOriginalQPackets.degree u
  let c := scaledCoordinates (R := R) (p := p) (L := L) u N
  obtain ⟨b, _, hb⟩ := QLocalPhysicalBirthInvoice.sheet R N p L (atoms) d c hL href
  refine ⟨ActualRunFullPages.prices R p L (atoms) d c b, ?_⟩
  intro j
  have e := ActualRunFullPages.entries R hG N p L hL (atoms) d c href b hb j
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

/-- One set of physical leaf kernels is chosen before testing. Only the actual
original OPE coefficient of each real/imaginary leaf changes with the tests. -/
theorem realized (href : ∀ s : Slot u, R.family.ref s.2.size ≤ L)
    (stock : Menu.Arsenal (fine)) (w : V → ℝ) (hw : ∀ i, 0<w i) :
    ∃ a : (Ω) → Bool × (index) → Menu.Hat (Stock.census V) (fine), ∀ x,
      ((ActualOriginalQInput.input Q D u μ orders hG N hL).leaf x).density =
        GapsLocal.Full.given (a x) 0 ∧
      ∃ C : ℝ, Menu.Offer (pos).origin (a x) w (fine).p.B ((fine).p.supportExponent-4) C := by
  obtain ⟨v, entry⟩ := entered D u hG N hL href
  let cap := QLocalPhysicalBirthMenu.sitePrice (fun j => Seal.scope (fine) ((rows) j).shellx)
    (fine).p.B (fun j => ((rows) j).due w (v j)) ((fine).p.supportExponent-4)
  have safe : MenuSafe (rows) (pos) v w cap := ⟨entry, hw, QLocalPhysicalBirthMenu.hit _ _ _ _
    (fun j => mul_nonneg (mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (Page.nonneg _ (entry j)))⟩
  let cards := FVA1.costume (rows) (pos) v w stock safe
  let hat (x : Ω) := MenuBridge.vital cards (fun i (_ : V→Unit) => (fees) i.2 x) (fun _=>())
  refine ⟨hat, ?_⟩
  intro x
  constructor
  · funext U
    rw [show ((ActualOriginalQInput.input Q D u μ orders hG N hL).leaf x).density U = _ from
        QlocalFinitePageTaste.density (rows) (pos) (fees) (fun j=> (entry j).stubs) x U]
    exact congrFun (FVA1.pegs (rows) (pos) v w stock safe (R.makes.wilson.represents N p L hL).good
      (fun i (_ : V→Unit) => (fees) i x) (fun _ _ => 0) (fun _=>())) U
  obtain ⟨offered,_⟩ := FVA1.price_cards (rows) (pos) v w stock safe
  refine ⟨_, fun i => offered.sites i, QLocalPhysicalBirthMenu.hit _ _ _ _ (fun _ => Menu.Crew w hw)⟩

end YM.Integration.WilsonOriginalOPEPageMenu
end

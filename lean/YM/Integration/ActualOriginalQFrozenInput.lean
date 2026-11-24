import YM.Integration.ActualOriginalQInput
import YM.Integration.ActualPacketCouplingFreeze

/-! Preselection coupling-freezing of the exact original-Q physical input.
The full Taste stays fixed. Its packet now reads the same original field
function at every formal coupling, and keeps the exact finite Paid bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQFrozenInput
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open MergeProof MergeProof.Accent
open ActualOriginalQReaders
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B)
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

def packets (N : ℕ) :=
  ActualPacketCouplingFreeze.freeze (ActualOriginalQPackets.packets Q D u μ orders N)
    (Pert.Asymptotics.regulatorRun R.family N p L)

/-- In particular the fixed clearing floor B=1 is available on every row. -/
theorem power_zero (N i : ℕ) : (packets Q D u μ orders N).power i = 0 := rfl

/-- The complete original coefficient-column field is independent of the
formal packet coupling; the configuration argument remains fully variable. -/
theorem packets_read (N : ℕ) (hL : L ≤ N) (g : ℝ)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    (packets Q D u μ orders N).read x g U =
      Mach (Stock.census V) (fun i =>
        ActualRunQlocalNativeTuple.reader D i (x i) *
          ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
            (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i)) := by
  unfold packets
  rw [ActualPacketCouplingFreeze.freeze_read,
    ActualOriginalQPackets.packets_read Q D u μ orders N hL]

/-- The same literal finite cost pays the frozen packet at every coupling. -/
theorem packets_paid (N : ℕ) (g : ℝ) (P : BudgetPoint)
    (w : V → ℝ) (width : ℝ) (hwidth : 0 < width) (hw : ∀ i, 0 < w i) :
    (packets Q D u μ orders N).Paid P (ActualOriginalQPackets.positions D u).stub
      (ActualRunQlocalNativeTuple.readerRegion D) w g width
      (ActualOriginalQPackets.packetCost Q D u μ orders N w width)
      (ActualOriginalQPackets.packetCover Q D u μ orders N P) 0 := by
  apply ActualPacketCouplingFreeze.freeze_paid
  exact ActualOriginalQPackets.packets_paid Q D u μ orders N P w width hwidth hw

variable [Nonempty V]

/-- The original full physical input has exactly the same factorization. -/
theorem density_packet_factor (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ s : Slot u, R.family.ref s.2.size ≤ L) (g : ℝ)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (U : Config G (R.family.side L p)) :
    ((ActualOriginalQInput.input Q D u μ orders hG N hL).leaf x).density U =
      ((R.family.path.rep N p L).eval U : ℂ) •
        Poly.pass ((packets Q D u μ orders N).read x g U) := by
  unfold packets
  rw [ActualPacketCouplingFreeze.freeze_read]
  exact ActualOriginalQInput.density_packet_factor Q D u μ orders hG N hL href x U

/-- Choose this packet and its genuine color convention before selecting M.
The original Taste and all original gas occurrences stay unchanged. -/
def packet_prepared (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ s : Slot u, R.family.ref s.2.size ≤ L)
    (colors : TestSpace (ActualRunQlocalNativeTuple.orbit D) →
      Comparison.RG02.Bulk.Colors (Stock.census V) G (R.family.side L p))
    (hColors : InputColors colors (packets Q D u μ orders N))
    (w cost : V → ℝ) (hw : ∀ i, 0 < w i) (hcost : ∀ i, 0 < cost i) :
    Global.Prepared N p L (ActualRunQlocalNativeTuple.packetCarrier R N p L hL)
      (ActualOriginalQPackets.positions D u).origin
      (ActualOriginalQInput.input Q D u μ orders hG N hL)
      colors (packets Q D u μ orders N) w (envelopeProduct cost) 0 :=
  Global.Prepared.of_bare_factorization N p L
    (ActualRunQlocalNativeTuple.packetCarrier R N p L hL)
    (ActualOriginalQPackets.positions D u).origin
    (ActualOriginalQInput.input Q D u μ orders hG N hL)
    colors (packets Q D u μ orders N) w (envelopeProduct cost)
    (fun i => (0 : (ActualRunQlocalNativeTuple.orbit D i).Mood))
    (ActualOriginalQInput.active_zero Q D u μ orders hG N hL) hColors hw
    (fun _ => Finset.prod_pos (fun i _ => hcost i)) (by rfl)
    (ActualRunQlocalNativeTuple.packet_gas_summable R N p L hL)
    (density_packet_factor Q D u μ orders hG N hL href
      (Pert.Asymptotics.regulatorRun R.family N p L))

end YM.Integration.ActualOriginalQFrozenInput
end

import YM.Integration.ActualRunQlocalTuplePayment
import YM.Integration.LocalComparisonBarePreparation

/-! Structural preparation of the same original native-tuple input.
The supplied InputColors convention remains explicit. No analytic vacuum,
cutoff-uniform payment, or complete PhysicalInput witness is asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQlocalNativeTuple
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open scoped Classical BigOperators

variable {G : Gauge}

/-- The entire original representation, with its actual norm receipt. -/
def packetCarrier (R : Run G) (N p L : ℕ) (hL : L ≤ N) :
    Global.StepCarrier R.family N p L where
  rep := R.family.path.rep N p L
  path := rfl
  clip := rfl
  point := (R.makes.wilson.represents N p L hL).vac

/-- Every original Nat-indexed gas occurrence is retained. -/
theorem packet_gas_summable (R : Run G) (N p L : ℕ) (hL : L ≤ N)
    (U : Config G (R.family.side L p)) :
    Summable (fun s : Finset ℕ =>
      ‖(R.family.path.rep N p L).activities.gasOccurrence
        (R.family.path.rep N p L).p s U‖) :=
  (YM.RG.Activities.gasSeries
    (R.makes.wilson.represents N p L hL).good.labels).absolute U

variable {R : Run G} {p L n : ℕ} {hn : n ≤ L} {V : Type}
  [DecidableEq V] [Fintype V] [Nonempty V]
  (D : Datum R p L n hn V)

/-- The exact all-test scalar factorization required by bare preparation. -/
theorem density_packet_factor (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, R.family.ref (grade D i) ≤ L)
    (x : TestSpace (orbit D)) (U : Config G (R.family.side L p)) :
    ((input D hG N hL).leaf x).density U =
      ((R.family.path.rep N p L).eval U : ℂ) •
        Poly.pass ((packets D N).read x
          (Pert.Asymptotics.regulatorRun R.family N p L) U) := by
  rw [density_packets D hG N hL href, mul_smul_comm, mul_one]

/-- The unchanged native-tuple Taste is prepared once its actual packet
color convention is supplied. Every independent envelope factor remains
explicit; the auxiliary remainder retains the full original vacuum gas. -/
def packet_prepared (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, R.family.ref (grade D i) ≤ L)
    (colors : TestSpace (orbit D) →
      Comparison.RG02.Bulk.Colors (Stock.census V) G (R.family.side L p))
    (hColors : InputColors colors (packets D N))
    (w cost : V → ℝ) (hw : ∀ i, 0 < w i) (hcost : ∀ i, 0 < cost i) :
    Global.Prepared N p L (packetCarrier R N p L hL) (positions D).origin
      (input D hG N hL) colors (packets D N) w (envelopeProduct cost) 0 :=
  Global.Prepared.of_bare_factorization N p L (packetCarrier R N p L hL)
    (positions D).origin (input D hG N hL) colors (packets D N)
    w (envelopeProduct cost) (fun i => (0 : (orbit D i).Mood))
    (active_zero D hG N hL) hColors hw
    (fun _ => Finset.prod_pos (fun i _ => hcost i)) (by rfl)
    (packet_gas_summable R N p L hL)
    (density_packet_factor D hG N hL href)

end YM.Integration.ActualRunQlocalNativeTuple
end

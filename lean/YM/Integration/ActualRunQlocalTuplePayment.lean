import YM.Integration.ActualRunQlocalTupleToken
import YM.Integration.NativeFinitePacketLaws
import YM.Integration.NativeFinitePacketPayment

/-! The literal native-reader packet family is paid by its complete finite
cost, at its actual regulator. No cutoff-uniform estimate is asserted.
The same packets factor the entire original-vacuum input density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQlocalNativeTuple
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof MergeProof.Accent
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {p L n : ℕ} {hn : n ≤ L}
  {V : Type} [DecidableEq V] (D : Datum R p L n hn V)

variable [Fintype V]

private structure Certificate (m : (Stock.census V).Mode) {q : ℕ}
    (T : Token G (R.family.side L p) (fun i => (orbit D i).Mood) q) : Prop where
  coefficient : 0 ≤ T.coin ∧ ∀ x : IndependentTests (orbit D),
    (∑ j, ‖T.gem j (testInclusion (orbit D) x)‖) ≤ T.coin
  paths : ∀ x : TestSpace (orbit D),
    (T.re x).length ≤ T.fall ∧ (T.re x).footprint T.root ⊆ T.plot
  addresses : ∀ v ∈ m.val, (positions D).stub v ⊆ T.plot
  symmetry : ∀ x U (k : G.El),
    T.touch x (fun i => G.adjoint k (U i)) = T.touch x U
  reads : ∀ j, Comparison.Density.Testing.Reads (readerRegion D) T.plot m.val (T.gem j)
  letter : ∀ j, RG3.Held.Letter ℂ (fun i => (orbit D i).Mood) m.val (T.gem j)

private theorem token_certificate (N : ℕ)
    (s : ActualRunKernelPackets.Index R (grade D)) :
    Certificate D ((Stock.census V).fire s.1) (packetToken D N s) := by
  refine ⟨⟨?_, token_bound D N s⟩, ?_, ?_, ?_, token_reads D N s, token_letter D N s⟩
  · let z : IndependentTests (orbit D) := fun i =>
      ⟨0, (Orbit.Bill.zero (U := orbit D i)).more zero_le_one⟩
    exact (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (token_bound D N s z)
  · intro x
    exact ⟨le_rfl, ActualRunKernelPackets.term_footprint R (orbit D) (grade D)
      N p L (root D) (packetLabels D) (coefficientBudget D) s⟩
  · intro v hv
    have he : v = s.1 := Finset.mem_singleton.mp hv
    subst v
    exact le_rfl
  · intro x U k
    simp only [packetToken, ActualRunKernelPackets.term,
      NativeCurvatureTensor.token_touch, NativeCurvatureTensor.value_invariant]

def packets (N : ℕ) :
    MarkedPackets (orbit D) G (R.family.side L p) (Stock.census V) :=
  ActualRunKernelPackets.packets R (Stock.census V) (orbit D) (grade D)
    N p L (root D) (packetLabels D) (coefficientBudget D)
    (fun i => (Stock.census V).fire i) (fun i => (Stock.census V).fire_hot i)

def packetCount : ℕ := Fintype.card (ActualRunKernelPackets.Index R (grade D))

def packetCost (N : ℕ) (w : V → ℝ) (width : ℝ) : ℝ :=
  NativeFinitePacketPayment.totalCost (packets D N) (packetCount D) w
    (Pert.Asymptotics.regulatorRun R.family N p L) width

def packetCover (N : ℕ) (B : BudgetPoint) : ℕ :=
  NativeFinitePacketPayment.coverOffset (packets D N) (packetCount D) B

private theorem certificates (N : ℕ) (i : ℕ)
    (T : Token G (R.family.side L p) (fun v => (orbit D v).Mood) ((packets D N).rank i))
    (hT : (packets D N).packet i = some T) :
    Certificate D ((packets D N).mode i) T := by
  unfold packets ActualRunKernelPackets.packets at hT ⊢
  exact MarkedPackets.ofFin_all _ _ _ _ _ _
    (fun m _ _ t => Certificate D m t)
    (fun _ => token_certificate D N _) i T hT

/-- Every original token law, full root address and independent-test bill
feeds the original Paid record. The displayed finite cost is not replaced
by a uniform constant; the cover reserve is the exact finite maximum. -/
theorem packets_paid (N : ℕ) (B : BudgetPoint) (w : V → ℝ) (width : ℝ)
    (hwidth : 0 < width) (hw : ∀ v, 0 < w v) :
    (packets D N).Paid B (positions D).stub (readerRegion D) w
      (Pert.Asymptotics.regulatorRun R.family N p L) width
      (packetCost D N w width) (packetCover D N B) 0 := by
  have hf : ∀ i, packetCount D ≤ i → (packets D N).packet i = none := by
    intro i hi
    unfold packets ActualRunKernelPackets.packets
    exact MarkedPackets.ofFin_absent _ _ _ _ _ _ i hi
  exact NativeFinitePacketPayment.paid (packets D N) (packetCount D) w
    (Pert.Asymptotics.regulatorRun R.family N p L) width B hf
    (positions D).stub (readerRegion D) hwidth hw
    (fun i T hT => (certificates D N i T hT).coefficient)
    (fun i T hT => (certificates D N i T hT).paths)
    (fun i T hT => (certificates D N i T hT).addresses)
    (fun i T hT => (certificates D N i T hT).symmetry)
    (fun i T hT => (certificates D N i T hT).reads)
    (fun i T hT => (certificates D N i T hT).letter)

/-- Exact full packet polynomial at the actual regulator, before any
coefficient extraction or independent-slot diagonalization. -/
theorem packets_read (N : ℕ) (hL : L ≤ N) (x : TestSpace (orbit D))
    (U : Config G (R.family.side L p)) :
    (packets D N).read x (Pert.Asymptotics.regulatorRun R.family N p L) U =
      Mach (Stock.census V) (fun i => reader D i (x i) *
        ActualRunPhysicalPages.kernel R N p L (grade D i) (label D i) (root D i) U) := by
  rw [packets, ActualRunKernelPackets.packets_read (hL := hL)]
  unfold Mach
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (Poly.send ((Stock.census V).fire i))
  exact congrFun
    ((Push.Local.presented (R.family.localSection (grade D i)) (root D i)
      (R.family.path.rep N p L).p.threshold).map_smul (reader D i (x i)) (label D i)) U

/-- The paid family factors the SAME original full-vacuum Taste for every
independent test. Formal-vacuum authentication and InputColors are separate. -/
theorem density_packets [Nonempty V] (hG : G.Simple) (N : ℕ) (hL : L ≤ N)
    (href : ∀ i, R.family.ref (grade D i) ≤ L)
    (x : TestSpace (orbit D)) (U : Config G (R.family.side L p)) :
    ((input D hG N hL).leaf x).density U =
      Poly.pass ((packets D N).read x
        (Pert.Asymptotics.regulatorRun R.family N p L) U) *
        (((R.family.path.rep N p L).eval U : ℂ) • (1 : Poly (Stock.census V))) := by
  rw [density_birth D hG N hL href, packets_read D N hL,
    mul_smul_comm, mul_one]
  rfl

end YM.Integration.ActualRunQlocalNativeTuple
end

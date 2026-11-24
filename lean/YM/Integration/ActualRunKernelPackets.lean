import YM.Integration.ActualRunCurvaturePackets
import YM.Integration.NativeFiniteMarkedPackets
import YM.Pert.Asymptotics.RawAxis

/-! Finite literal packets for the original Run's unmasked kernels.
The field rank and every threshold factor remain explicit.  The coefficient
contains the fixed actual regulator to that rank; at that same nonzero
regulator it cancels the packet's negative coupling power.  This identifies
the full input for every test and field, without identifying an independently
prescribed all-coupling formal family or asserting a sharp price. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunKernelPackets
open Function Finset Lattice Wilson RG Source Labels Marker
open PertExtension Comparison.Density.RenderM
open PhysicalNext.Repeat.Legato
open NativeCurvatureTensor ActualRunCurvaturePackets LocalComparison
open scoped Classical BigOperators

variable {G : Gauge} (A : Run G)
variable {V : Type} [DecidableEq V] (C : Census V)
  (D : V → ComparisonDensity.Address.Orbit)
variable {I : Type} [Fintype I] (d : I → ℕ)

/-- Every coordinate and every supported monomial of the original section. -/
abbrev Index :=
  (i : I) × (j : (A.family.labels.level (d i)).Index) ×
    ↥(((ofRun A (d i)).data.shape j).support)

def tokenRank (s : Index A d) : ℕ := s.2.2.val.sum fun _ k => k

def fieldRank (s : Index A d) : ℕ :=
  ActualRunGradedKernels.rank A (d s.1) s.2.1

omit [Fintype I] in
theorem term_grade (s : Index A d) : fieldRank A d s ≤ tokenRank A d s := by
  exact (ofRun A (d s.1)).data.low s.2.1 s.2.2.val s.2.2.property

variable (N p L : ℕ)

theorem regulator_pos (hL : L ≤ N) :
    0 < Pert.Asymptotics.regulatorRun A.family N p L := by
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  exact lt_of_lt_of_le (half_pos (WardBin.hot _ _))
    (A.makes.wilson.represents N p L hL).band.1

def weight (s : Index A d) : ℂ :=
  ((((A.family.path.rep N p L).p.threshold)⁻¹ ^
    fieldRank A d s : ℝ) : ℂ) *
      MvPolynomial.coeff s.2.2.val ((ofRun A (d s.1)).data.shape s.2.1)

variable (o : I → Site (A.family.side L p))
  (v : (i : I) → TestSpace D → A.family.label (d i))
  (B : (i : I) → (A.family.labels.level (d i)).Index → ℝ)

def amplitude (s : Index A d) (x : TestSpace D) : ℂ :=
  ((Pert.Asymptotics.regulatorRun A.family N p L : ℂ) ^ fieldRank A d s *
    weight A d N p L s) * v s.1 x s.2.1

def term (s : Index A d) :
    Token G (A.family.side L p) (fun a => (D a).Mood) (tokenRank A d s) :=
  NativeCurvatureTensor.token
    (fun k => (word s.2.2.val k).2) (o s.1)
    (fun k => (ofRun A (d s.1)).data.columns s.2.1 (word s.2.2.val k).1)
    ((A.family.localSection (d s.1)).footprint (o s.1))
    (amplitude A D d N p L v s)
    (‖(Pert.Asymptotics.regulatorRun A.family N p L : ℂ) ^ fieldRank A d s *
      weight A d N p L s‖ * B s.1 s.2.1)

def scalarValue (s : Index A d) (x : TestSpace D)
    (U : Config G (A.family.side L p)) : ℂ :=
  weight A d N p L s * v s.1 x s.2.1 *
    value (fun k => (word s.2.2.val k).2)
      (fun k => ((ofRun A (d s.1)).data.columns s.2.1
        (word s.2.2.val k).1).atSite U (o s.1))

omit [DecidableEq V] [Fintype I] in
theorem term_read (hL : L ≤ N) (s : Index A d) (x : TestSpace D)
    (U : Config G (A.family.side L p)) :
    (Pert.Asymptotics.regulatorRun A.family N p L : ℂ) ^
        (-(fieldRank A d s : ℤ)) *
      (term A D d N p L o v B s).read x U =
      scalarValue A D d N p L o v s x U := by
  have hz : (Pert.Asymptotics.regulatorRun A.family N p L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (regulator_pos A N p L hL).ne'
  have hc :
      (Pert.Asymptotics.regulatorRun A.family N p L : ℂ) ^
          (-(fieldRank A d s : ℤ)) *
        (Pert.Asymptotics.regulatorRun A.family N p L : ℂ) ^ fieldRank A d s = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hz)]
  unfold term
  rw [NativeCurvatureTensor.token_read]
  let z : ℂ := Pert.Asymptotics.regulatorRun A.family N p L
  let w : ℂ := weight A d N p L s
  let t : ℂ := value (fun k => (word s.2.2.val k).2)
    (fun k => ((ofRun A (d s.1)).data.columns s.2.1
      (word s.2.2.val k).1).atSite U (o s.1))
  change z ^ (-(fieldRank A d s : ℤ)) *
    (t * ((z ^ fieldRank A d s * w) * v s.1 x s.2.1)) =
      w * v s.1 x s.2.1 * t
  calc
    _ = (z ^ (-(fieldRank A d s : ℤ)) * z ^ fieldRank A d s) *
      (w * v s.1 x s.2.1 * t) := by ac_rfl
    _ = _ := by rw [hc, one_mul]

omit [DecidableEq V] [Fintype I] in
theorem term_bound (s : Index A d) (x : TestSpace D)
    (hx : ‖v s.1 x s.2.1‖ ≤ B s.1 s.2.1) :
    (∑ j, ‖(term A D d N p L o v B s).gem j x‖) ≤
      (term A D d N p L o v B s).coin := by
  apply NativeCurvatureTensor.token_price
  change ‖(_ : ℂ) * v s.1 x s.2.1‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

omit [DecidableEq V] [Fintype I] in
theorem term_footprint (s : Index A d) :
    (⟨(term A D d N p L o v B s).path, fun _ => 0⟩ :
      Atom G (tokenRank A d s)).footprint (o s.1) ⊆
        (A.family.localSection (d s.1)).footprint (o s.1) := by
  exact basis_footprint (ofRun A (d s.1)) s.2.1 s.2.2.val (o s.1)

/-- All tests share this finite packet layout.  Only actual padding is absent. -/
def packets (mode : I → C.Mode) (hm : ∀ i, mode i ≠ C.quiet) :
    MarkedPackets D G (A.family.side L p) C :=
  let e := (Fintype.equivFin (Index A d)).symm
  MarkedPackets.ofFin
    (fun k => mode (e k).1)
    (fun k => tokenRank A d (e k))
    (fun k => -(fieldRank A d (e k) : ℤ))
    (fun k => term A D d N p L o v B (e k))
    (fun k => hm (e k).1)
    (fun k => by
      have h := term_grade A d (e k)
      omega)

private theorem send_sum {ι : Type*} [Fintype ι] (m : C.Mode) (f : ι → ℂ) :
    Poly.send m (∑ i, f i) = ∑ i, Poly.send m (f i) := by
  ext j
  simp only [Poly.part_send, Poly.part_sum]
  by_cases h : j = m <;> simp [h]

omit [DecidableEq V] [Fintype I] in
private theorem sum_values (i : I) (x : TestSpace D)
    (U : Config G (A.family.side L p)) :
    (∑ j : (A.family.labels.level (d i)).Index,
      ∑ m : ↥(((ofRun A (d i)).data.shape j).support),
        scalarValue A D d N p L o v ⟨i, j, m⟩ x U) =
      ActualRunPhysicalPages.kernel A N p L (d i) (v i x) (o i) U := by
  rw [run_kernel]
  apply Finset.sum_congr rfl
  intro j _
  let f : ((Fin ((ofRun A (d i)).data.count j) × G.ColorIndex) →₀ ℕ) → ℂ :=
    fun m =>
      (((((A.family.path.rep N p L).p.threshold)⁻¹ ^
        ActualRunGradedKernels.rank A (d i) j : ℝ) : ℂ) *
        MvPolynomial.coeff m ((ofRun A (d i)).data.shape j)) * v i x j *
      value (fun k => (word m k).2)
        (fun k => ((ofRun A (d i)).data.columns j (word m k).1).atSite U (o i))
  calc
    _ = ∑ m : ↥(((ofRun A (d i)).data.shape j).support), f m.val := by
      rfl
    _ = ∑ m ∈ ((ofRun A (d i)).data.shape j).support, f m :=
      Finset.sum_coe_sort _ f
    _ = _ := by
      unfold basisValue
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      dsimp only [f]
      ring

theorem packets_read [Fintype V] (mode : I → C.Mode)
    (hm : ∀ i, mode i ≠ C.quiet) (hL : L ≤ N)
    (x : TestSpace D) (U : Config G (A.family.side L p)) :
    (packets A C D d N p L o v B mode hm).read x
      (Pert.Asymptotics.regulatorRun A.family N p L) U =
      ∑ i : I, Poly.send (mode i)
        (ActualRunPhysicalPages.kernel A N p L (d i) (v i x) (o i) U) := by
  let e := (Fintype.equivFin (Index A d)).symm
  rw [packets, MarkedPackets.ofFin_read]
  calc
    _ = ∑ s : Index A d, Poly.send (mode s.1)
        (scalarValue A D d N p L o v s x U) := by
      apply Fintype.sum_equiv e
      intro k
      exact congrArg (Poly.send (mode (e k).1))
        (term_read A D d N p L o v B hL (e k) x U)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_sigma]
      simpa only [send_sum] using
        congrArg (Poly.send (mode i)) (sum_values A D d N p L o v i x U)

end YM.Integration.ActualRunKernelPackets

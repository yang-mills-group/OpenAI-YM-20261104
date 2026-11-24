import YM.Integration.WilsonSeparatedDiagnosticFrames
import YM.RG16.Unmasked.Pace

/-! The manuscript's displaced diagnostic on the original reporting mesh:
r=a_m Λ_m^B, and independently normalized incoming slots at
a_m Λ_m^(b_i), 0≤b_i≤B.  In particular b_i=0 uses the actual reporting
length a_m in every ordinary physical pivot slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedReportedGram
open Function Filter Set Lattice Wilson Cells Spec Climb OPE OPE.Orbits OPE.Cards PhysMS
open Frontier6.Road Trace.Pilot SharedIntrinsicWilsonGrid ContinuumIntrinsicWilsonProduct IntrinsicWilsonTensor
open WilsonSeparatedDiagnosticGram
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ}

def length (C:Family G) (B:ℝ) (m:ℕ) : ℝ :=
  (RG16.Lambda C.path.levels m)^B*C.S.a m

theorem reporting (C:Family G) (m:ℕ) : length C 0 m=C.S.a m := by
  rw [length,Real.rpow_zero,one_mul]

private theorem small (C:Family G) (hG:G.Simple) (B:ℝ) : Tendsto (length C B) atTop (𝓝 0) := by
  change Tendsto (fun m=>(RG16.Lambda C.path.levels m)^B*C.S.a m) atTop (𝓝 0)
  simpa only [RG16.Literal.Upper,sub_add_cancel,one_mul] using
    RG16.Literal.cluster_shrinks C hG 1 (B-1) zero_lt_one

def inputs (J : ℝ → tower S) (m:ℕ) (B:ℝ) (b:I→ℝ) (v:(i:I)→Input C (d i)) (i:I) : Input C (d i) :=
  (J (length C B m) (d i)).symm (J (length C (b i) m) (d i) (v i))

/-- A true full correlation/Gram at displaced diagnostic length, measured
against the literal unit-channel coefficient of the common captured
finite cutoff. The normalized mixed input columns can be chosen after it. -/
theorem original (F : Final C f S) (fac : Facilities C f S) (anchor:I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C 0 (Fintype.card I) (∑ i,d i)) (J : ℝ → tower S) (H : Leading F J)
    {M η σ B : ℝ} (ηp : 0<η) (roomFor : σ<1/32) {g : ℝ → ℝ} (hg : Coupling G g)
    (k:ℕ) {ε:ℝ} (εp : 0<ε) :
    ∀ᶠ m:ℕ in atTop, let r := length C B m
      ∀ x : I → Cover, WithinRoom r M η (C.S.gridPoint (P.j r) ∘ x) 0 →
      (∃ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z) ∧
      ∀ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z →
        let y := C.S.gridPoint (P.j r) ∘ x
        ∀ b : I → ℝ,(∀ i,b i∈Icc (0:ℝ) B) → ∀ q : Viewers F,q=none ∨ Screen y →
          ∀ v : (i:I)→Input C (d i),let a := inputs J m B b v
          Cluster F Q J a r (P.b r) (P.j r) x (Z a) ∧
          ‖Orbits.moment (spectator F q) y (fun i=>J (length C (b i) m) (d i) (v i))-
              scalar S S (S.project 0 (Z a))‖ ≤ ε*g r^k*r^σ*∏ i,‖v i‖ := by
  have pos (s:ℝ) (m:ℕ) : 0<length C s m := mul_pos
    (Real.rpow_pos_of_pos (RG16.Literal.lambda_pos C m) s) (C.S.a_pos _)
  have time : Tendsto (length C B) atTop trail :=
    tendsto_nhdsWithin_iff.mpr ⟨small C fac.simpleGate B,Eventually.of_forall (pos B)⟩
  have buy := time.eventually (WilsonSeparatedDiagnosticFrames.original F fac anchor Q P J H ηp roomFor
    (A:=1) zero_le_one hg k εp (M:=M))
  have twice := (small C fac.simpleGate (B+B)).eventually_lt_const zero_lt_one
  filter_upwards [buy,twice] with m row clearance r x room
  have bundle := row x room
  refine ⟨bundle.1,?_⟩
  intro Z has y b exponents q channel v a
  let L := RG16.Lambda C.path.levels m
  have lp : 0<L := RG16.Literal.lambda_pos C m
  have big : 1≤L := one_le_two.trans (RG16.Literal.lambda_up C m).le
  let t (i:I) := L^(b i-B)
  have hp : 0<L^B := Real.rpow_pos_of_pos lp B
  have lower : r ≤ (L^B)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ hp).mpr
    change (L^B*C.S.a m)*L^B≤1
    rw [show (L^B*C.S.a m)*L^B=L^(B+B)*C.S.a m by rw [Real.rpow_add lp]; ring]
    exact clearance.le
  have wall (i:I) : t i∈Icc (r^(1:ℝ)) 1 := by
    rw [Real.rpow_one]
    constructor
    · calc
        _ ≤ (L^B)⁻¹ := lower
        _ = L^(-B) := (Real.rpow_neg lp.le _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le big (by linarith only [(exponents i).1])
    · exact Real.rpow_le_one_of_one_le_of_nonpos big (sub_nonpos.mpr (exponents i).2)
  have located (i:I) : t i*r=length C (b i) m := by
    change L^(b i-B)*(L^B*C.S.a m) = L^(b i)*C.S.a m
    rw [←mul_assoc,←Real.rpow_add lp,sub_add_cancel]
  have same : WilsonSeparatedDiagnosticFrames.inputs J r t v=a := by
    funext i
    change (J r (d i)).symm (J (t i*r) (d i) (v i)) = _
    rw [located i]
    rfl
  have get := bundle.2 Z has t wall q channel v
  change Cluster F Q J (WilsonSeparatedDiagnosticFrames.inputs J r t v) r _ _ x
      (Z (WilsonSeparatedDiagnosticFrames.inputs J r t v)) ∧
    ‖Orbits.moment (spectator F q) y (fun i=>J (t i*r) (d i) (v i))-scalar S S
      (S.project 0 (Z (WilsonSeparatedDiagnosticFrames.inputs J r t v)))‖ ≤ _ at get
  simpa only [same,located] using get

end YM.Integration.WilsonSeparatedReportedGram

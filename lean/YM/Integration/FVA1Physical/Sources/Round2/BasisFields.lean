import YM.Integration.FVA1Physical.Sources.Round2.ConditionalFields
import YM.Integration.FVA1Physical.Wilson.FieldHorizon

/-! Top physical moments of the same canonical C18 basis stencils as those
used by the formal Wilson step, including both cutoff powers and the actual
conditional denominator. -/

namespace YM.Integration.FVA1Physical.Round2

open MeasureTheory Lattice RG YM.Wilson YM.Precision YM.Exterior Source Extra.Histories LocalLTE.Sail MergeProof
open FormalOPE.RG10.InversionTop Comparison.RG02 PhysicalNext.Repeat.Legato
open YM.Integration.FVA1Physical.Wilson
open scoped BigOperators

/-- The physical basis and transfer data may come directly from a calibrated
C18 purchase, including an invoice bought jointly with other RG tasks. -/
structure StencilFamily (G : Gauge) where
  path : History G
  ref : ℕ → ℕ
  factory : ∀ d N n, TransferData ((Labels.frames G).level d) path N n
  makes : (Family.mk path (Next.Foundations.hol G) (Labels.frames G) (Next.Foundations.localSection G) ref factory).Makes

noncomputable def StencilFamily.family {G : Gauge} (A : StencilFamily G) :=
  Family.mk A.path (Next.Foundations.hol G) (Labels.frames G) (Next.Foundations.localSection G) A.ref A.factory

noncomputable def StencilFamily.ofRun {G : Gauge} (A : Run G) : StencilFamily G :=
  ⟨A.family.path, A.t, A.stories, A.makes⟩

variable {G : Gauge} {I : Type} [Fintype I] [DecidableEq I] (A : StencilFamily G) {d : ℕ}
variable (a : I → FieldLabel A.family d) (N n : ℕ) (o : ∀ k, I → Site (A.family.side k n))

/-- An unsmeared, unrotated canonical physical batch of unit basis sources. -/
noncomputable def basisBatch : Batch A.family.path N n I where
  demand j := (a j).1.val
  voice j := Pi.single (a j).2 1
  motion _ := Motion.nil
  origin := o

omit [DecidableEq I] [Fintype I] in
theorem basis_wavelength (j : I) (u : Config G (A.family.side N n)) :
    (basisBatch A a N n o).wavelengths j u =
      ((A.family.path.levels.clock.threshold N)⁻¹ ^ MSMatch.SourceTop.grade (placeLabels a (o N)) j) •
        MSMatch.SourceTop.field (placeLabels a (o N)) j u := by
  let F := (Labels.frames G).level (a j).1.val
  let k : F.Index := (a j).2
  let e := (F.grades k).2
  let θ := A.family.path.levels.clock.threshold N
  let C := A.family.localSection (a j).1.val
  let z := (A.family.S.a N : ℂ) ^ (a j).1.val
  have hz : z ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (A.family.S.a_pos _).ne')
  have he : F.scaled θ⁻¹ (Pi.single k 1) = ((θ⁻¹ ^ e : ℝ) : ℂ) • (Pi.single k 1) := by
    classical
    ext l
    by_cases h : l = k
    · subst l; simp [e]
    · simp [Pi.single_eq_of_ne h]
  change z * (z⁻¹ * C.places (F.scaled θ⁻¹ (Pi.single k 1)) 0 (pull (1 : Signed) (o N j) u)) =
    (θ⁻¹ ^ e) • C.places (Pi.single k 1) (o N j) u
  rw [← mul_assoc,mul_inv_cancel₀ hz,one_mul,pull_one,C.places_trans,zero_add,he]
  exact congrFun (((C.eval_linear.mk' _).map_smul ((θ⁻¹ ^ e : ℝ) : ℂ) (Pi.single k 1))) _

variable {m : ℕ} (B : Marker.Census I)

/-- Convert the engineering/source cutoff normalization to the independent
Wilson normalization on each physical source, at the measured bare coupling. -/
noncomputable def basisFactor (s : B.Mode) :=
  let g := Pert.Asymptotics.regulatorRun A.family (m+1) n (m+1)
  let θ := A.family.path.levels.clock.threshold (m+1)
  ∏ j ∈ s.val, (g / θ) ^ MSMatch.SourceTop.grade (placeLabels a (o (m+1))) j

private theorem path_one (H : History G) (n m : ℕ) (f : Config G (H.S.side (m+1) n) → ℂ) :
    conditionalPath H (m+1) n f m (Nat.le_succ m) = conditionalPush H (m+1) n m f := by
  calc
    _ = conditionalPush H (m+1) n m (conditionalPath H (m+1) n f (m+1) le_rfl) :=
      Nat.decreasingInduction_succ_left ..
    _ = _ := by rw [conditionalPath,Nat.decreasingInduction_self]

omit [Fintype I] in
theorem basis_moment_eq_torus (s : B.Mode) (x : fieldDir G (A.family.side m n) 1) :
    let Y := basisBatch A a (m+1) n o
    let V := placeLabels a (o (m+1))
    let g := Pert.Asymptotics.regulatorRun A.family (m+1) n (m+1)
    (momentTable B Y m (Nat.le_succ _) (Integral.sample g x)).part s =
      basisFactor A a n o B (m := m) s •
        ((MSMatch.SourceTop.torusVacuum (C := A.family) m n x g)⁻¹ • MSMatch.SourceTop.torusFull m n V x s.val g) := by
  let H := A.family.path
  let S := H.levels.clock.op m n
  let Y := basisBatch A a (m+1) n o
  let V := placeLabels a (o (m+1))
  let g := Pert.Asymptotics.regulatorRun A.family (m+1) n (m+1)
  let θ := H.levels.clock.threshold (m+1)
  let β := H.β (m+1) n (m+1)
  let z := basisFactor A a n o B (m := m) s
  have hg := (Local.RealStep.coupling_pos A.family (m+1) n (m+1) A.makes le_rfl).ne'
  have ht : Integral.temperature g = β := Local.RealStep.trajectory A.family (m+1) n (m+1) A.makes le_rfl
  have htop : (H.rep (m+1) n (m+1)).eval = bare β := (A.makes.wilson.starts (m+1) n).2
  have hnext : (H.rep (m+1) n m).eval = S.push β (H.rep (m+1) n (m+1)).eval := (A.makes.wilson.steps (m+1) n m (Nat.lt_succ_self _)).1
  have he (u : Config G (A.family.side (m+1) n)) :
      (∏ j ∈ s.val, Y.wavelengths j u) = z • (∏ j ∈ s.val, (g ^ MSMatch.SourceTop.grade V j)⁻¹ • MSMatch.SourceTop.field V j u) := by
    have h₁ (j : I) : Y.wavelengths j u =
        (((g/θ) ^ MSMatch.SourceTop.grade V j : ℝ) : ℂ) *
          ((g ^ MSMatch.SourceTop.grade V j)⁻¹ • MSMatch.SourceTop.field V j u) := by
      change (basisBatch A a (m+1) n o).wavelengths j u = _
      rw [basis_wavelength]
      change (θ⁻¹ ^ MSMatch.SourceTop.grade V j) • MSMatch.SourceTop.field V j u = _
      have scale (e : ℕ) : θ⁻¹ ^ e = (g/θ)^e * (g^e)⁻¹ := by
        rw [← inv_pow, ← mul_pow]
        congr 1
        rw [div_eq_mul_inv,mul_right_comm,mul_inv_cancel₀ hg,one_mul]
      rw [scale,mul_smul]
      rfl
    calc
      _ = ∏ j ∈ s.val, (((g/θ) ^ MSMatch.SourceTop.grade V j : ℝ) : ℂ) *
        ((g ^ MSMatch.SourceTop.grade V j)⁻¹ • MSMatch.SourceTop.field V j u) := Finset.prod_congr rfl (fun j _ => h₁ j)
      _ = _ := by rw [Finset.prod_mul_distrib]; change _ = ((∏ j ∈ s.val, (g/θ) ^ MSMatch.SourceTop.grade V j : ℝ) : ℂ)*_; rw [Complex.ofReal_prod]
  dsimp only
  change conditionalPath H (m+1) n (fun u => ∏ j ∈ s.val, Y.wavelengths j u) m (Nat.le_succ m) (Integral.sample g x) = _
  rw [path_one]
  unfold conditionalPush MSMatch.SourceTop.torusFull MSMatch.SourceTop.torusVacuum
  change ((H.rep (m+1) n m).eval (Integral.sample g x))⁻¹ • S.push β
      (fun u => (H.rep (m+1) n (m+1)).eval u • ∏ j ∈ s.val, Y.wavelengths j u) (Integral.sample g x) =
    z • ((S.push (Integral.temperature g) (bare (Integral.temperature g)) (Integral.sample g x))⁻¹ • S.push (Integral.temperature g) (fun u => (bare (Integral.temperature g) u : ℂ) * ∏ j ∈ s.val, (g ^ MSMatch.SourceTop.grade V j)⁻¹ • MSMatch.SourceTop.field V j u) (Integral.sample g x))
  rw [hnext,htop,ht]
  change ((S.push β (bare β) (Integral.sample g x))⁻¹ : ℝ) • S.push β
      (fun u => bare β u • ∏ j ∈ s.val, Y.wavelengths j u) (Integral.sample g x) = _
  let Z : Config G (A.family.side (m+1) n) → ℂ :=
    fun u => bare β u • ∏ j ∈ s.val, (g ^ MSMatch.SourceTop.grade V j)⁻¹ • MSMatch.SourceTop.field V j u
  have hZ : (fun u => bare β u • ∏ j ∈ s.val, Y.wavelengths j u) = fun u => z • Z u := by
    funext u
    rw [he]
    exact smul_comm (bare β u) z _
  have ec (v : Config G (A.family.side m n)) : (S.push β (fun u => z • Z u) v) = z • S.push β Z v := by
    simp only [StepData.push,smul_comm (_ : ℝ) z,integral_smul]
  rw [hZ,ec]
  change _ • (z • S.push β Z (Integral.sample g x)) = z • ((_ : ℝ) • S.push β Z (Integral.sample g x))
  exact smul_comm _ z _

end YM.Integration.FVA1Physical.Round2

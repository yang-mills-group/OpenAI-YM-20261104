import YM.Integration.WilsonPositionOriginalDiagnosticRightReading
import YM.Slice.Reflection
import YM.Cells.Polar

/-! The mixed-clock right fee on a reflected original Wilson Gram. Its left
cutoff column is controlled by its genuine separated self-reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticReflected
open Finset Filter Set MeasureTheory Lattice Wilson RG Cells PhysicalNext.Repeat.Legato
open MS MS.Land MS.Menus MS.Local.Physical
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckPrescriptionFields
open WilsonPositionOriginalDiagnosticRightAssay WilsonPositionOriginalDiagnosticRightReading
open WilsonPositionOriginalDiagnosticRightSeries WilsonPositionProgramReporterBand
open Spec Table PhysMS RG17 Extraction Extraction.Order OPE.Therm
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
local notation "I"=>Glyph B h

theorem rawInterior (N per d:ℕ)(v:R.family.label d)(o:Site (R.family.side N per))
    {K:Set (Site (R.family.side N per))}(covers: ↑((R.family.localSection d).footprint o)⊆K) :
    Interior K (R.family.O N per v o):=by
  apply Interior.enlarges (K:=((R.family.localSection d).footprint o)) _ covers
  have cont:=R.family.continuousO N per d v o
  exact ⟨R.family.invariant R.makes N per d v o,cont.measurable,
    R.family.localO N per d v o,cont.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩

theorem addRows {n:Side}{J:Type*}(s:Finset J){K:Set (Site n)}{A:J → Config G n → ℂ}
    (good:∀a∈s,Interior K (A a)):Interior K (fun U=>∑a∈s,A a U):=by
  induction s using Finset.induction_on with
  | empty=>simpa using Interior.constant (G:=G) K 0
  | @insert a s fresh step=>
    simpa [fresh] using (good a (mem_insert_self _ _)).plus (step fun b hb=>good b (mem_insert_of_mem hb))

theorem markedInterior (μ ν:ℝ)(p:ℕ)(x:ℂ)(N per:ℕ)(j:I)(o:Site (R.family.side N per))
    {K:Set (Site (R.family.side N per))} (fits:∀a:I,↑((R.family.localSection a.size).footprint o)⊆K):
    Interior K (remainder R Q h μ ν p x N per j o):=by
  have pay(α:ℝ)(a:I):Interior K (posted R Q h α p x N per a o):=by
    apply addRows (univ:Finset I);intro b _
    simpa only [WilsonMatrixOriginalDeckPrescriptionFields.raw,mul_comm] using Interior.scale ((sources Q h α p b a).eval x)
      (rawInterior R N per b.size (WilsonMacroscopicRichOriginalPortfolio.label R N per b) o (fits b))
  have head:Interior K (fun U=>∑b:I,posted R Q h μ p x N per b o U*(change Q h μ ν p b j).eval x):=by
    apply addRows (univ:Finset I);intro b _
    simpa only [mul_comm] using Interior.scale ((change Q h μ ν p b j).eval x) (pay μ b)
  change Interior K (fun U=>(∑b:I,submitted R Q h μ p x N per b o U*(change Q h μ ν p b j).eval x)-submitted R Q h ν p x N per j o U)
  simp_rw [fields]
  simpa only [neg_one_mul,sub_eq_add_neg] using head.plus (Interior.scale (-1) (pay ν j))

/-- At the microscopic date the physical Wilson history and the Gibbs law
on which the native reflection form is positive have the same measure. -/
theorem same (N per:ℕ):scene R.family.path N per N=Wilson.law G (R.family.side N per) (R.family.beta N per):=by
  unfold scene Wilson.law
  congr 1;funext U
  have start:(R.family.path.rep N per N).eval=bare (R.family.path.β N per N):=(R.makes.wilson.starts N per).2
  simp only [dose,Wilson.weight,start,Family.beta]

theorem paid {N per:ℕ}(cut:Cut (R.family.side N per))(E X:Config G (R.family.side N per) → ℂ)
    (b:ℝ)(epos:0≤b)(right:Interior cut.sector E)(left:Interior cut.sector X)(bill:∀U,‖E U‖≤b):
    let ρ:=scene R.family.path N per N
    ‖∫U,E U*star (X (cut.pullC G U)) ∂ρ‖^2 ≤ b^2*‖∫U,X U*star (X (cut.pullC G U)) ∂ρ‖:=by
  dsimp only
  have hot:0<R.family.beta N per:=Overlay.beta_positive R.makes.wilson (m:=N) (N:=N) (p:=per) le_rfl
  have cs:=Cells.cauchy (Slice.reflected_positive cut _ hot.le) right left
  have self:‖Cells.form (R.family.beta N per) cut E E‖≤b^2:=by
    have all(U:Config G (R.family.side N per)):‖E U*star (E (cut.pullC G U))‖≤b^2:=by
      rw [norm_mul,norm_star,pow_two]
      exact mul_le_mul (bill _) (bill _) (norm_nonneg _) epos
    simpa [Cells.form,Wilson.moment] using
      norm_integral_le_of_norm_le_const (μ:=Wilson.law G (R.family.side N per) (R.family.beta N per)) (ae_of_all _ all)
  rw [same]
  exact cs.trans (mul_le_mul_of_nonneg_right self (norm_nonneg _))

/-- The retained left deposit may have an arbitrarily large bare field cap.
The bound uses its own separated reflected finite Wilson correlator. -/
theorem original {D:XSpace.Run}{stage:ℕ}(T:Band R D stage)(simple:G.Simple)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)(L:Layout F){A:ℝ}(pos:0≤A):
    ∃C:ℝ,0≤C ∧ ∀p:ℕ,∀ᶠt:ℕ in atTop,∀ N per,T.reporter+t≤N→∀θ ψ:ℝ,‖θ‖+‖ψ‖≤A→∀j:I,
      ∀cut:Cut (R.family.side N per),∀o z:Site (R.family.side N per),∀d:ℕ,
      (∀a:I,↑((R.family.localSection a.size).footprint o)⊆cut.sector)→
      ↑((R.family.localSection d).footprint z)⊆cut.sector→∀r:ℝ,∀w:R.family.label d,
      let τ:=R.family.S.scale (T.reporter+t+T.upper t)-R.family.S.scale (T.reporter+t)
      let y:=Pert.Asymptotics.regulatorRun R.family N per (T.reporter+t)
      let E:=remainder R Q h (θ-τ) (ψ-τ) (p+2) (y:ℂ) N per j o
      let X:=deposited R F L d r w N per z
      let ρ:=scene R.family.path N per N
      ‖∫U,E U*star (X (cut.pullC G U)) ∂ρ‖^2 ≤
        (C*y^(p+1))^2*‖∫U,X U*star (X (cut.pullC G U)) ∂ρ‖:=by
  obtain ⟨C,cpos,purchase⟩:=WilsonPositionOriginalDiagnosticRightPrimitive.original R Q h T simple A pos
  refine ⟨C,cpos,?_⟩
  intro p
  filter_upwards [purchase p] with t due
  intro N per live θ ψ room j cut o z d rightFits leftFits r w τ y E X ρ
  have yPos:0<y:=ActualRunKernelPackets.regulator_pos R N per (T.reporter+t) live
  have epos:0≤C*y^(p+1):=mul_nonneg cpos (pow_nonneg yPos.le _)
  have bill(U:Config G (R.family.side N per)):‖E U‖≤C*y^(p+1):=by
    dsimp only [E,remainder];simp_rw [fields]
    exact due N per live θ ψ room j o U
  have right:Interior cut.sector E:=markedInterior R Q h _ _ _ _ N per j o rightFits
  have left:Interior cut.sector X:=rawInterior R N per d _ z leftFits
  exact paid R cut E X _ epos right left bill

end YM.Integration.WilsonPositionOriginalDiagnosticReflected

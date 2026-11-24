import YM.Integration.WilsonPublicOutputDetector

/-! Recover the complete running physical packet from the full ordinary comparison and a
finite family of lower and upper two-point comparisons at the same external radius. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputRows
open Filter Set Table Spec OPE OPE.Orbits OPE.Log PhysMS Trace.Pilot Climb
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale Pert Pert.Position MS MS.Local.Physical
open MS.Menus MS.Land MS.Theater RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
local notation "Print" => Press.portDeck G
local notation "formal" => WilsonMacroscopicRichMSCoefficient.field
local notation "fee" => WilsonMacroscopicRichMSCoefficient.coefficient

def axis (h : ℕ) (b : Glyph Print h) : (Bel R.family.book).Field h :=
  (exactField R.family.labels h).symm (Daylight Print h b)

/-- All entries of the prescribed finite order, including those below the requested grade. -/
theorem printed (h : ℕ) (M : MS_Data G (Position.OpenAxis.Plot Print))
    {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → (Bel R.family.book).Field (d i))
    (μ : ℝ) (x : Points n) (t : ℝ) (q : ℕ) :
    formal R M h d v μ x t q = ∑ b : Glyph Print h, fee R M d v μ x t q b • axis (R:=R) h b := by
  simp [WilsonMacroscopicRichMSCoefficient.field, axis]

def packet (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {n : ℕ} (h : ℕ) (d : Fin n → ℕ) (v : (i : Fin n) → (Bel R.family.book).Field (d i))
    (r : ℝ) (x : Points n) : S.Field h :=
  Q.packet h (fun i => r • x i) (Frame.born J r v) 0

private lemma sum_error {I E : Type} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : I → ℂ) (X Y : I → E) :
    ‖(∑ i, c i • X i) - ∑ i, c i • Y i‖ ≤ ∑ i, ‖c i‖ * ‖X i-Y i‖ := by
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖c i • X i - c i • Y i‖ := norm_sum_le _ _
    _ = _ := by simp only [← smul_sub, norm_smul]

/-- The ticket that issues the sharp physical expansion and the detector act on the same
final hierarchy. At each requested order the discrepancy is charged to the full ordinary
measurement, the independent spatial expansion, and the signed two-point columns. -/
theorem original {Y : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac : Facilities R.family f S) {l : Filter (ℕ×ℕ)} [l.NeBot] (lo : l ≤ f.fuse)
    (bill : MatrixTicket (C:=R.family) S F.sector.derivatives l) (h : ℕ) :
    LogTrace F Q.port ∧
    ∃ B : Profiles R h, ∃ w : B.probes.index → Atom (R:=R) h,
      ∃ issued : ∀ j, B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℝ), Coupling G g → ∀ P E A : ℕ, P+E ≤ A →
      ∀ᶠ r in trail, let t := r / ((g r)^A)^2
      ∃ tp : 0 < t, ∀ (M : MS_Data G (Position.OpenAxis.Plot Print)) (n : ℕ)
        (d : Fin n → ℕ) (v : (i : Fin n) → (Bel R.family.book).Field (d i))
        (x : Points n) (μ coupling : ℝ) (q : ℕ)
        (joint : B.probes.index → ℂ) (gram : Glyph Print h → B.probes.index → ℂ)
        (C D : ℝ), 0 ≤ C →
        let obs := sample F J Z B w issued tp r x (fun i => ⟨d i,v i⟩)
        let measured := packet F J Q h d v r x
        let a := fun b : Glyph Print h => fee R M d v μ x coupling q b
        let bills := ‖obs-joint‖ + ‖joint-∑ b, a b • gram b‖ +
          ∑ b, ‖a b‖ * ‖gram b - row F J Z B t (J r h (axis (R:=R) h b))‖
        ‖row F J Z B t measured - obs‖ ≤ C * (((g r)^A)^2)^(h+1) / (g r)^E →
        bills ≤ D*(g r)^(P+A*(2*h+1)) →
        ‖(J r h).symm measured - formal R M h d v μ x coupling q‖ ≤ K*(C+D)*(g r)^P := by
  refine ⟨OPE.tickets_suffice F fac lo bill Q.spans,?_⟩
  obtain ⟨B,w,issued,K,kp,invoice⟩ := WilsonPublicOutputDetector.original F J Z lead owed simple h
  refine ⟨B,w,issued,K,kp,?_⟩
  intro g hg P E A room
  filter_upwards [invoice g hg A,hg.positive,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)]
    with r data gp cap
  intro t
  obtain ⟨tp,read⟩ := data
  refine ⟨tp,?_⟩
  intro M n d v x μ coupling q joint gram C D cp obs measured a bills sharp residual
  let y := formal R M h d v μ x coupling q
  let U := row F J Z B t
  let field (b : Glyph Print h) := U (J r h (axis (R:=R) h b))
  have printedRow : U (J r h y) = ∑ b, a b • field b := by
    rw [show y = ∑ b : Glyph Print h, a b • axis (R:=R) h b from printed h M d v μ x coupling q,
      map_sum,map_sum]
    simp only [map_smul,field]
  have three : ‖obs - U (J r h y)‖ ≤ bills := by
    rw [printedRow]
    calc
      _ ≤ ‖obs-joint‖ + ‖joint-∑ b, a b • gram b‖ + ‖(∑ b, a b • gram b)-∑ b, a b • field b‖ :=
        (norm_sub_le_norm_sub_add_norm_sub _ (∑ b, a b • gram b) _).trans
          (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ joint _) _)
      _ ≤ _ := add_le_add_right (sum_error a gram field) _
  have cost := read n x (fun i => ⟨d i,v i⟩) measured (J r h y)
  rw [map_sub,LinearEquiv.symm_apply_apply] at cost
  exact WilsonPublicOutputDetector.powers gp cap kp cp P E A h room
    (cost.trans (mul_le_mul_of_nonneg_left (add_le_add sharp (three.trans residual)) kp))
end YM.Integration.WilsonPublicOutputRows

import YM.Integration.WilsonPositionOriginalDiagnosticReflected
import YM.Integration.WilsonPositionOriginalDiagnosticHalfSpace

/-! The signed right-source substitution against a complete, dressed and
smeared original field. Both test placements use the actual fine lattice at
each fixed physical radius before either regulator is removed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticReflectedTest
open Filter Finset Set MeasureTheory Lattice Wilson RG Cells MS MS.Land MS.Menus MS.Local.Physical
open PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalDeckRawMoment WilsonPositionOriginalDiagnosticRightReading
open WilsonPositionOriginalDiagnosticReflected WilsonPositionOriginalDiagnosticHalfSpace
open WilsonPositionProgramReporterBand Spec Table PhysMS RG17 Extraction Extraction.Order OPE.Therm
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
local notation "I"=>Glyph B h

def mix {n:Side}{k:ℕ}(a:Fin k → ℂ)(A:Fin k → Config G n → ℂ)(U:Config G n):ℂ:=∑i,a i*A i U

private theorem supports {k:ℕ}{n:Side}(K:Set (Site n))(a:Fin k → ℂ)(A:Fin k → Config G n → ℂ)
    (ok:∀i,Interior K (A i)):Interior K (mix a A):=by
  exact addRows univ fun i _=>Interior.scale _ (ok i)

private theorem size {k:ℕ}{n:Side}(a:Fin k → ℂ)(A:Fin k → Config G n → ℂ)(c:ℝ)
    (ok:∀i U,‖A i U‖≤c)(U:Config G n):‖mix a A U‖≤(∑i,‖a i‖)*c:=by
  calc _ ≤ ∑i,‖a i*A i U‖:=norm_sum_le .. 
       _ ≤ ∑i,‖a i‖*c:=by
         apply sum_le_sum;intro i _;rw [norm_mul];exact mul_le_mul_of_nonneg_left (ok _ _) (norm_nonneg _)
       _ = _ :=by rw [sum_mul]

private theorem offset {N:ℕ}{r:ℝ}(a:Axis)(e:Cover)
    (small:(e a).natAbs*R.family.S.a N≤r/4):(e a).natAbs≤width R r N:=by
  apply Nat.le_floor
  dsimp only [Schedule.a] at small
  have den:0<((R.family.S.denominator N).val:ℝ):=by exact_mod_cast (R.family.S.denominator N).property
  field_simp at small;linarith

theorem original {D:XSpace.Run}{stage:ℕ}(T:Band R D stage)(simple:G.Simple)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)(L:Layout F){A:ℝ}(allow:0≤A):
    ∃C:ℝ,0≤C ∧ ∀p:ℕ,∀ᶠt:ℕ in atTop,∀θ ψ:ℝ,‖θ‖+‖ψ‖≤A → 
      ∀cap:ℕ,h≤cap → ∀a:Axis,∀r:ℝ,0<r → r≤1 → ∀ᶠN:ℕ in atTop,∀per:ℕ,
      T.reporter+t≤N → ∀o:Site (R.family.side N per),∀k l:ℕ,∀s:Fin k → Cover,∀z:Fin l → Cover,
      (∀i,(s i a).natAbs*R.family.S.a N≤r/4) → (∀i,(z i a).natAbs*R.family.S.a N≤r/4) → 
      ∀(d:Fin l → ℕ), (∀i,d i≤cap) → ∀(dclock:Fin l → ℝ)(w:∀i,R.family.label (d i))
      (j:Fin k → I)(α:Fin k → ℂ)(β:Fin l → ℂ),
      let cut:=sheet R N per a o (2*width R r N)
      let τ:=R.family.S.scale (T.reporter+t+T.upper t)-R.family.S.scale (T.reporter+t)
      let y:=Pert.Asymptotics.regulatorRun R.family N per (T.reporter+t)
      let E:=mix α (fun i=>remainder R Q h (θ-τ) (ψ-τ) (p+2) (y:ℂ) N per (j i)
        (wrap (R.family.side N per) (s i)+o))
      let X:=mix β (fun i=>deposited R F L (d i) (dclock i) (w i) N per
        (wrap (R.family.side N per) (z i)+o))
      let ρ:=scene R.family.path N per N
      ‖∫U,E U*star (X (cut.pullC G U)) ∂ρ‖^2≤
        ((∑i,‖α i‖)*(C*y^(p+1)))^2*‖∫U,X U*star (X (cut.pullC G U)) ∂ρ‖:=by
  obtain ⟨C,cpos,purchase⟩:=WilsonPositionOriginalDiagnosticRightPrimitive.original R Q h T simple A allow
  refine ⟨C,cpos,?_⟩;intro p
  filter_upwards [purchase p] with t due
  intro θ ψ room cap includes a r small short
  filter_upwards [paid_width R cap a small short] with N widthOK
  intro per live o k l s z sf zf d dcap dc w j α β cut τ y E X ρ
  obtain ⟨below,above⟩:=widthOK per
  have yPos:0<y:=ActualRunKernelPackets.regulator_pos R N per (T.reporter+t) live
  apply paid R cut E X _ (mul_nonneg (sum_nonneg fun _ _=>norm_nonneg _) (mul_nonneg cpos (pow_nonneg yPos.le _)))
  · apply supports
    intro i
    apply markedInterior
    intro q
    exact places R a o (s i) ((Nat.le_of_lt_succ q.1.isLt).trans includes) below above (offset R a _ (sf i))
  · apply supports
    intro i
    apply rawInterior
    exact places R a o (z i) (dcap i) below above (offset R a _ (zf i))
  · apply size
    intro i U
    dsimp only [remainder];simp_rw [fields]
    exact due N per live θ ψ room (j i) _ U

end YM.Integration.WilsonPositionOriginalDiagnosticReflectedTest

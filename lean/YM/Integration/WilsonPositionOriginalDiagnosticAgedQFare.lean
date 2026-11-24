import YM.Integration.WilsonPositionOriginalDiagnosticRightPrimitive

/-! The two-clock stencil is bounded on every independently chosen physical mesh. Its numerical coupling is sampled on the elected original reporter and upper cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticAgedQFare
open Finset Filter Lattice Wilson RG PhysicalNext.Repeat.Legato MS MS.Land MS.Menus MS.Local.Physical
open Source Marker Precision FullQLocal LocalComparison
open WilsonMatrixOriginalDeckPrescriptionFields WilsonMatrixOriginalDeckPrescriptionGrowth
open WilsonPositionProgramReporterBand WilsonPositionOriginalDiagnosticRightSeries
open WilsonPositionOriginalDiagnosticRightAssay
open scoped Classical Topology BigOperators Real
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B)(h:ℕ)
variable {D:XSpace.Run} {stage:ℕ} (T:Band R D stage)
local notation "I" => Glyph B h
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "Δ" t => R.family.S.scale (T.reporter+t+T.upper t)-R.family.S.scale (T.reporter+t)

open private clocks from YM.Integration.WilsonPositionOriginalDiagnosticRightPrimitive

theorem original (simple:G.Simple)(A:ℝ)(low:0≤A):
    ∃C:ℝ,0≤C ∧ ∀p:ℕ, ∀ᶠt:ℕ in atTop,∀N per,T.reporter+t≤N→
      ∀θ ψ:ℝ,‖θ‖+‖ψ‖≤A→∀date:ℕ,∀j:I,∀o:Site (R.family.side date per),∀U:Config G (R.family.side date per),
      let μ:=θ-(Δ t)
      let ν:=ψ-(Δ t)
      let y:=Pert.Asymptotics.regulatorRun R.family N per (T.reporter+t)
      let x:ℂ:=y
      ‖∑b:I,posted R Q h μ (p+2) x date per b o U*(change Q h μ ν (p+2) b j).eval x -
        posted R Q h ν (p+2) x date per j o U‖ ≤ C*y^(p+1):=by
  have issued (a:I):∃c:ℝ,0≤c ∧ ∀(N per:ℕ)(o:Site (R.family.side N per))(U:Config G (R.family.side N per)),
      ‖raw (B:=B) R h N per o U a‖≤c :=by
    obtain ⟨b,bd⟩:=(Envelope.compactC ((R.family.localSection a.size).continuous_evaluate
      (ActualOriginalDictionary.coordinates R B a.size a.grade a.2.2))).cost
    refine ⟨max 0 b,le_max_left ..,?_⟩
    intro N per o U
    rw [raw,WilsonMacroscopicRichOriginalPortfolio.label,RGComparison.Core16.Descent.field_label_correct]
    exact (bd _).trans (le_max_right ..)
  choose c hn enabled using issued
  refine ⟨∑a:I,c a,sum_nonneg fun i _=>hn i,?_⟩
  intro p
  have original:=WilsonPositionOriginalDiagnosticRightClock.original R Q h simple (A+7) (by linarith) 2 p
  have late:Tendsto (fun t:ℕ=>T.reporter+t) atTop atTop:=tendsto_atTop_mono (fun t=>Nat.le_add_left ..) tendsto_id
  filter_upwards [late.eventually original] with t bank
  intro N per live θ ψ available date j o U μ ν y x
  have fee:=bank N per live μ ν (clocks R T t available)
  let field:=raw (B:=B) R h date per o U
  change ‖∑b:I,(∑a:I,field a*(sources Q h μ (p+2) a b).eval x)*(change Q h μ ν (p+2) b j).eval x -
     ∑a:I,field a*(sources Q h ν (p+2) a j).eval x‖≤_
  simp only [sum_mul,mul_assoc]
  rw [sum_comm];simp_rw [←mul_sum];rw [←sum_sub_distrib];simp_rw [←mul_sub]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum;intro a _
  rw [norm_mul]
  exact mul_le_mul (enabled a date per o U) (fee a j) (norm_nonneg _) (hn a)

end YM.Integration.WilsonPositionOriginalDiagnosticAgedQFare

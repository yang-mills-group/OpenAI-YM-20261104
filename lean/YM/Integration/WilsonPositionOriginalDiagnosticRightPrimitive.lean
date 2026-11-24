import YM.Integration.WilsonPositionOriginalDiagnosticRightClock
import YM.Integration.WilsonPositionOriginalDiagnosticRightAssay
import YM.Integration.WilsonMacroscopicRichGridCofactors
import YM.Integration.WilsonPositionProgramReporterBand

/-! The complete mixed-clock fee contrast on the original group field on the
reporter's chosen auxiliary calendar, uniformly in its physical cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRightPrimitive
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

private theorem span (t:ℕ): (Δ t)=(T.index t:ℝ)*Real.log D.ratio:=by
  have ratio:=congrArg Real.log (T.spacing t)
  rw [Real.log_div (R.family.S.a_pos _).ne' (R.family.S.a_pos _).ne'] at ratio
  have den : Real.log (D.step (T.index t)).spacing= -((T.index t:ℝ)*Real.log D.ratio):=by
    change Real.log ((D.den (T.index t):ℝ)⁻¹)=_
    simp [XSpace.Run.den,Real.log_pow]
  rw [den] at ratio
  simp only [Schedule.scale,Real.log_inv];linarith only [ratio]

private theorem clocks (t:ℕ){A θ ψ:ℝ}(slack:‖θ‖+‖ψ‖≤A):
    size (θ-(Δ t)) (ψ-(Δ t)) ≤ (A+7)*(1+Λ (T.reporter+t))^2 :=by
  let X:=Λ (T.reporter+t)
  have small:1≤X:=by change 1≤2+Real.log _;linarith only [Real.log_nonneg (R.family.path.levels.fits.delayed (T.reporter+t)).le]
  have positive:0≤Δ t:= (Real.rpow_nonneg (zero_le_one.trans small) _).trans (T.floor t) |>.trans_eq (span R T t).symm
  have broad:(Δ t)≤X^2+2*X:=by
    rw [span]
    have shape:X^((3:ℝ)/2)≤X^2:=by
      rw [←Real.rpow_natCast X 2];exact Real.rpow_le_rpow_of_exponent_le small (by norm_num)
    exact (T.ceiling t).trans (add_le_add shape (le_refl (2*X)))
  have a:0≤A:=(add_nonneg (norm_nonneg _) (norm_nonneg _)).trans slack
  have left:=norm_sub_le θ (Δ t)
  have right:=norm_sub_le ψ (Δ t)
  have nd:‖(Δ t)‖=(Δ t):=by rw [Real.norm_eq_abs,abs_of_nonneg positive]
  rw [nd] at left right
  unfold size
  change 1+‖θ-(Δ t)‖+‖ψ-(Δ t)‖≤(A+7)*(1+X)^2
  nlinarith only [left,right,slack,broad,small,a,mul_nonneg a (sq_nonneg X),mul_nonneg a (zero_le_one.trans small),sq_nonneg X]

/-- The priced remainder is a uniform all-field comparison for the true
registered primitives, including the scalar and every lower right field. -/
theorem original (simple:G.Simple)(A:ℝ)(low:0≤A):
    ∃C:ℝ,0≤C ∧ ∀p:ℕ, ∀ᶠt:ℕ in atTop,∀N per,T.reporter+t≤N→
      ∀θ ψ:ℝ,‖θ‖+‖ψ‖≤A→∀j:I,∀o:Site (R.family.side N per),∀U:Config G (R.family.side N per),
      let μ:=θ-(Δ t)
      let ν:=ψ-(Δ t)
      let y:=Pert.Asymptotics.regulatorRun R.family N per (T.reporter+t)
      let x:ℂ:=y
      ‖∑b:I,posted R Q h μ (p+2) x N per b o U*(change Q h μ ν (p+2) b j).eval x -
        posted R Q h ν (p+2) x N per j o U‖ ≤ C*y^(p+1):=by
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
  intro N per live θ ψ available j o U μ ν y x
  have fee:=bank N per live μ ν (clocks R T t available)
  let field:=raw (B:=B) R h N per o U
  change ‖∑b:I,(∑a:I,field a*(sources Q h μ (p+2) a b).eval x)*(change Q h μ ν (p+2) b j).eval x -
     ∑a:I,field a*(sources Q h ν (p+2) a j).eval x‖≤_
  simp only [sum_mul,mul_assoc]
  rw [sum_comm];simp_rw [←mul_sum];rw [←sum_sub_distrib];simp_rw [←mul_sub]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum;intro a _
  rw [norm_mul]
  exact mul_le_mul (enabled a N per o U) (fee a j) (norm_nonneg _) (hn a)

end YM.Integration.WilsonPositionOriginalDiagnosticRightPrimitive

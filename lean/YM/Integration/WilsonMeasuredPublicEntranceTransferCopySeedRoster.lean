import YM.Integration.WilsonMeasuredPublicEntranceTransferCopySeedFare
/-! One price before both regulators for the actual uncropped finite word. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopySeedRoster
open Finset Real Wilson Lattice RG Source Labels Extra.Multi PhysicalNext.Repeat.Legato
open WilsonOriginalPublicTrialPhaseFiling (reserve)
open WilsonOriginalPublicTrialPhaseRate (wage)
open WilsonMeasuredPublicEntranceTransferCopySeedFare (capital)
open WilsonOriginalMicroscopicEntranceOpticalUnits (rank)
open WilsonPositionProgramBlockedTrialAddBack (names)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "H" K:arg => (C).path.levels.clock.hatBeta K

theorem original {I:Type}[Fintype I](d:I→ℕ)(load:ℕ)(z:ℝ)(T:I→ℝ)(pos:∀i,0≤T i)(e:I→ℕ):
    ∃ D E:ℕ,∃C₀:ℝ,1≤C₀ ∧ (∀i,d i≤D) ∧ ∀K N p:ℕ,K≤N →
      ∀o:I→Site ((C).side K p),∀v:∀i,(C).label (d i),
      ((C).path.levels.budget K).supportExponent≤z →
      (∀i,((C).labels.level (d i)).coeffSize (v i)≤T i*(H K)^(e i)) →
      let B:=fun i=>capital R (d i) load z (T i)*(H K)^(16+(rank R (d i)+e i))
      ∀i,let P:=(C).path.rep N p K
         let S:=(C).localSection (d i)
         let D₀:=S.footprint (o i)
         let F:=(C).labels.level (d i)
         let M:=BasisCost.price S*F.coeffSize (names R (d i) N p K (v i))
         let κ:=(C).path.levels.clock.forcedAllowance K
         1≤B i ∧ B i≤C₀*(H K)^E ∧ F.coeffSize (v i)≤B i ∧
           P.p.mass D₀ 0+2*(D₀.card:ℝ)*sqrt κ*P.p.mass D₀ M≤B i ∧
           (wage P.p.B load (reserve R (N:=N) (d i) (o i) (v i)))⁻¹≤B i:=by
  classical
  let tag i:=16+(rank R (d i)+e i)
  let E:=∑i,tag i
  let C₀:=1+∑i,|capital R (d i) load z (T i)|
  have co:1≤C₀:=le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=>abs_nonneg _))
  refine ⟨∑i,d i,E,C₀,co,fun i=>Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i),?_⟩
  intro K N p live o v support funds B i
  have receipt:=WilsonMeasuredPublicEntranceTransferCopySeedFare.original R live (d i) load (o i) (v i)
     (pos i) (e i) support (funds i)
  refine ⟨receipt.1,?_,receipt.2⟩
  have tags:tag i≤E:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have caps:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>|capital R (d j) load z (T j)|) (fun j _=>abs_nonneg _) (Finset.mem_univ i)
  have one:1≤H K:=(R.family.path.levels.fits.delayed K).le
  exact mul_le_mul ((le_abs_self _).trans (show |capital R (d i) load z (T i)|≤C₀ by dsimp only [C₀];linarith))
    (pow_le_pow_right₀ one tags) (pow_nonneg (zero_le_one.trans one) _) (zero_le_one.trans co)
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopySeedRoster
end

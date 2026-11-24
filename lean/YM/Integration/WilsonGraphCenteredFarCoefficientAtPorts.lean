import YM.Integration.WilsonGraphCenteredFarBilinearBook

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCoefficientAtPorts
open Function PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphPublishedShapeEstimate WilsonGraphPreElectedShapeEstimates
open scoped BigOperators Classical
universe u
variable (g : GaugeGroup) (hg : g.IsSimple)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev S := _root_.IssuedBridge.PostedAppointedConversion.filed
  (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching (Teller.logNu 1)

private theorem recover (a b : ℕ → ℂ) (all : ∀ p : ℕ, ∑ i ∈ range (p+1),a i = ∑ i ∈ range (p+1),b i)
    (j : ℕ) : a j = b j := by
  cases j with
  | zero => simpa using all 0
  | succ j =>
    have step := all (j+1)
    rw [sum_range_succ a (j+1),sum_range_succ b (j+1),all j] at step
    exact add_left_cancel step

theorem coefficient (h j : ℕ) (y : Spacetime) (hy : WithLp.toLp 2 ![0,y] ∈ YM.conf 2)
    (a b : Sec g.core h) :
    coeff j (Reg.Point.story (book (Z g hg) h 2 ⟨WithLp.toLp 2 ![0,y],hy⟩) ![a,b]) =
      WilsonGraphStandaloneCorrelation.converted (S.{u} g hg) j
        (publicLetters (fun _ : Fin 2 => h) ![a,b]) (WithLp.toLp 2 ![0,y]) := by
  apply recover (fun i => coeff i (Reg.Point.story (book (Z g hg) h 2
    ⟨WithLp.toLp 2 ![0,y],hy⟩) ![a,b])) (fun i =>
      WilsonGraphStandaloneCorrelation.converted (S.{u} g hg) i
        (publicLetters (fun _ : Fin 2 => h) ![a,b]) (WithLp.toLp 2 ![0,y]))
  intro p
  have same := AppointedCenteredRows.centeredCrop.{u} g hg h p a b y 1 hy
  rw [AppointedBilinearBook.appointed g hg h y hy a b] at same
  simp only [YM.FVA2.GradedFar.crop_eq,Complex.ofReal_one,one_pow,one_mul] at same
  refine same.trans ?_
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => WilsonGraphStandaloneCorrelation.converted
    (S.{u} g hg) i (publicLetters (fun _ : Fin 2 => h) ![a,b]) (WithLp.toLp 2 ![0,y])) (p+1)

theorem basis (h j : ℕ) (y : Spacetime) (hy : WithLp.toLp 2 ![0,y] ∈ YM.conf 2)
    (c : Fin 2 → Dime g.core h) :
    coeff j (Reg.Point.story (book (Z g hg) h 2 ⟨WithLp.toLp 2 ![0,y],hy⟩)
      (fun i => dime g.core h (c i))) =
      WilsonGraphStandaloneCorrelation.converted (S.{u} g hg) j
        (publicLetters (fun _ : Fin 2 => h) ![dime g.core h (c 0),dime g.core h (c 1)])
        (WithLp.toLp 2 ![0,y]) := by
  have roster : (fun i => dime g.core h (c i)) = ![dime g.core h (c 0),dime g.core h (c 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [roster]
  exact coefficient.{u} g hg h j y hy _ _

end YM.FVA2.GradedFar.AppointedCoefficientAtPorts

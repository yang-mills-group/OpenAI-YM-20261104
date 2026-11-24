import YM.Integration.WilsonIndependentCollarOutputFilm
import YM.Integration.WilsonIndependentCollarActualTeacher

/-! The exact rooted Book consumed by the original physical path census at
the current chronological successor, with each earlier scalar retained. -/
set_option autoImplicit false
set_option maxHeartbeats 310000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarConnectedFilm
open Function Finset Filter Lattice Wilson RG Precision PhysicalNext.Repeat.Legato Exterior Work.F08 MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonIndependentCollarRootedWidth WilsonIndependentCollarPrintIncome
open FundedMarkedPathSelection WilsonOlderFreshConnectedRobe
open private dressed from YM.Integration.WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e m N:ℕ} {A:ℝ} {S J:Finset ι}

theorem original (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(X:Input Q hm S k D A)
    (w:Widths G)(c:ι)(pin:c∈J)(sub:J⊆S)(pos:0≤A)(live:m<N)(school:Cloze D k Q Credit.leanC):
    let U:=Q.mint m hm
    let l:=mass k J
    let out:=issue w (e+1) l U.gear
    let t:=rooted J.card out.strip
    let mark:=FundedMarkedPathSelection.price Q k D A J m
    let salary:=glacier G l (e+1)*(Real.exp (3*U.σ/8)*(out.fee*mark))*sprigs J c (U.σ/2)
    U.gear.s=2*U.σ → U.σ≤1 →
      (∀y,Rendered Q hm X J c l N y) ∧ ∀o j,j ≤ e → ∀r:Fin (l+j+1),
        Rooted Q hm X J c l N t salary o j r:=by
  intro U l out t mark salary twice cap
  have board:=fun y=>ready X sub pos live school y
  have actual:Vσ Q m hm=U.σ:=min_eq_right cap
  have raw (y)(j:ℕ)(hj:j<e+1)(r):Wig Bank.terrain y U.σ mark J ((output X J N y).2 j r):=by
    rw [←actual];exact (board y).2 j hj r
  have good:0 ≤ mark:=mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth m hm))) (pow_nonneg pos _)
  obtain ⟨openT,narrow,span,_⟩:=WilsonIndependentCollarRootedWidth.original w U.gear U.σ U.width twice (e+1) l J.card
  have printed (y):=WilsonIndependentCollarTeacherPrint.original U.gear U.σ U.width twice w l
    (e+1) (e+1) le_rfl (output X J N y) (board y).1 J y c pin mark good (raw y) t openT span narrow
  refine ⟨fun y j hj=>(printed y).2.2 j (by omega),?_⟩
  intro o j hj r
  have small:j<e+1:=by omega
  obtain ⟨μ,born,ink⟩:=WilsonIndependentCollarRootedInk.original U.gear U.σ U.width twice w l
    (e+1) (e+1) le_rfl J c pin (output X J N) (fun y=>(board y).1) mark good raw o j small r
  refine ⟨μ,born,?_,ink,fun _ hg h1=>dressed ink j l r hg h1⟩
  intro x test n field root
  apply Rolls.packet _ test _ _ (born x) field root
  exact (((printed (toe J c o x.1)).1.2 j small).2 r).1 x.2

end YM.Integration.WilsonIndependentCollarConnectedFilm
end

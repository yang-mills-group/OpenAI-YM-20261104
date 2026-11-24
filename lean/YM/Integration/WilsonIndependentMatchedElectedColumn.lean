import YM.Integration.WilsonIndependentMatchedElectedSection
import YM.Integration.WilsonIndependentMatchedCensusReceipt
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Both parts of the fitted column on the same dated receipt, including
the lower field's actual common-horizon multiplier and the complete unit. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedElectedColumn
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08
open Wilson Tree Precision AnalyticNext.QuarticMatch.Sheets Exterior Next.Free
open Gauge Source Labels XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.StableStrip PertExtension RegulatorIR
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedOrdinaryProfile (stems)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedCoveredSeats (seat)
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{H:Hol G}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
variable {h D k e u d:ℕ}{E A K U:Credit}{v:Rails h k u e}
variable {s:Bool}{p:h<D}{w:d<D}(M:Master H)
variable (X:CutsP H (M.T h) p v E A K U)(L:Torch H (M.T h) p v E A K)(run:XSpace.Run)
  (base idx f:ℕ)(amp δ η fee:ℝ)(c:Verse (R.family.labels.level d))

theorem actual (booked:Filed X L run base idx f amp δ η fee (Shrine (plate (sectionAt R W s d) w) c))(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)(n:Side):
    let x:=paceT X.ax.S X.m (X.m+X.i)
    Blue.flash ((word ((a/amp) • X.pt) φ x y o h).1 n)=
        stems R W n s w (a • c) φ x y o h ∧
    Blue.flash ((receiving X (a/amp) φ y o X.i).1 n)=
        WilsonIndependentMatchedElectedSection.profile (M.T h) p n ((a/amp) • X.tileP) φ x y o h ∧
    Blue.flash ((seat X (a/amp) φ y o X.i).1 n)=stems R W n s w (a • c) φ x y o h-
        WilsonIndependentMatchedElectedSection.profile (M.T h) p n ((a/amp) • X.tileP) φ x y o h :=by
  let x:=paceT X.ax.S X.m (X.m+X.i)
  have hx:0<x:=pace_pos ..
  have top:X.N=X.ceilC:=by
    change X.N=X.m+X.i
    rw [booked.top,booked.report,booked.gap,WilsonIndependentEvenPassport.count,Nat.add_assoc]
  have src:X.Ntop=plate (M.T h) p:=WilsonIndependentMatchedTopStencils.initial X top
  have one:Blue.flash ((word ((a/amp) • X.pt) φ x y o h).1 n)=
        stems R W n s w (a • c) φ x y o h:=by
    rw [booked.actual a,←shrine_μ]
    exact WilsonIndependentMatchedOrdinaryProfile.original R W n s w _ φ x y o h hx
  have printed:receiving X (a/amp) φ y o X.i=word (Shrine (plate (M.T h) p) ((a/amp) • X.tileP)) φ x y o h:=by
    rw [WilsonIndependentMatchedFittedSeat.inlet,src,shrine_μ]
  have two:Blue.flash ((receiving X (a/amp) φ y o X.i).1 n)=
        WilsonIndependentMatchedElectedSection.profile (M.T h) p n ((a/amp) • X.tileP) φ x y o h:=by
    rw [printed]
    exact WilsonIndependentMatchedElectedSection.original (M.T h) p H (M.spec h) (M.pop h) n _ φ x y o h hx
  have ⟨_,_,paid⟩:=WilsonIndependentMatchedFiledIncome.original (M.T h) p H (M.spec h) (M.pop h) le_rfl 0 0
  have shelf:Auth h (receiving X (a/amp) φ y o X.i):=by
    rw [printed]
    exact locale_val _ (Mer.placed h φ ((paid _).1) x y) o
  have stable:Auth k (seat X (a/amp) φ y o X.i):=(WilsonIndependentMatchedCoveredSeats.traced X (a/amp) φ y o).1 _ le_rfl
  have split:=congrArg (fun Z:Era G ℝ=>Blue.flash (Z.1 n))
    (WilsonIndependentMatchedTotalTop.placed X (a/amp) φ y o)
  change Blue.flash ((word ((a/amp) • X.pt) φ x y o h).1 n)=
    Blue.flash ((seat X (a/amp) φ y o X.i).1 n+(receiving X (a/amp) φ y o X.i).1 n) at split
  rw [one,flash_add (finite_shell (stable.span n)) (finite_shell (shelf.span n)),two] at split
  exact ⟨one,two,eq_sub_of_add_eq split.symm⟩

end YM.Integration.WilsonIndependentMatchedElectedColumn

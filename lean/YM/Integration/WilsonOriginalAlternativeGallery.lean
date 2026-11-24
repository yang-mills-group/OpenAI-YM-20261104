import YM.Integration.WilsonOriginalAlternativeLog
import YM.Integration.WilsonOriginalAlternativeHard
import YM.Integration.WilsonOriginalAlternativeExtraction

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeGallery
open Function Finset Set Lattice Wilson RG Ac Marker QuadraticLocal Push.Corrected Push.AbsoluteSums MeasureTheory
open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {n:Side} {T I J:Type} {o:V→Site n} {P:RG.Rep G n}
variable (A:Gallery T I o P R) (C:Lamps T J G P.p (o∘Prod.fst) (board R))

def issued : Gallery T (WilsonOriginalAlternativeLamps.roster A.E ⊕ J) (o∘Prod.fst) P (board R) :=
  ⟨(WilsonOriginalAlternativeLamps.issued A.E).join C,WilsonOriginalAlternativeHard.issued A.K⟩

theorem price {w:V→ℝ} (wp:∀i,0<w i) {a e b κ:ℝ} (fund:A.Pays w a e κ)
    (extra:C.Paid (wallet R w) P.p.B a b) :
    (issued A C).Pays (wallet R w) a (e+b) κ :=
  ⟨Lamps.joinPaid (WilsonOriginalAlternativeLamps.paid A.E wp fund.budget) extra,
    WilsonOriginalAlternativeHard.paid A.K wp fund.wages⟩

private theorem reorder {B:Type} [CommRing B] [Algebra ℂ B] (c:ℂ) (x y z:B) :
    c • ((x*y)*z)=(c • (x*z))*y :=
  (congrArg (c • ·) (mul_right_comm x y z)).trans (smul_mul_assoc c (x*z) y).symm

theorem original {w:V→ℝ} (wp:∀i,0<w i) {a e b κ:ℝ} (ha:0≤a) (fund:A.Pays w a e κ)
    (extra:C.Paid (wallet R w) P.p.B a b) (t:T) (U:Config G n) (F:V→ℂ)
    (guard:C.log t U=ink R F) :
    (issued A C).density t U=stamped R (A.density t U) F := by
  have old:=WilsonOriginalAlternativeLamps.paid A.E wp fund.budget
  have opt:=positive R wp
  have n₀:=A.E.quiet_of_hasSum t U (fund.budget.sums ha wp t U)
  have n₁:((inheritAll R (A.E.log t U)).part (board R).quiet)=0:=(quiet R _).trans n₀
  have n₂:=C.quiet_of_hasSum t U (extra.sums ha opt t U)
  have gas:(issued A C).gas t U=inheritAll R (A.gas t U):=
    WilsonOriginalAlternativeHard.entire A.K wp ha fund.wages t U
  have reg:(issued A C).E.log t U=inheritAll R (A.E.log t U)+C.log t U:=
    (Lamps.joinLog t U (old.sums ha opt t U) (extra.sums ha opt t U)).trans
      (congrArg (·+C.log t U) (WilsonOriginalAlternativeLog.original A.E wp ha fund.budget t U))
  unfold Gallery.density stamped
  rw [gas,reg,Extra.Trajectories.pass_add n₁ n₂,map_smul,map_mul,
    Multi.pass_map (inheritAll R) _ n₀ n₁,← guard]
  exact reorder _ _ _ _

theorem true_read {w:V→ℝ} (wp:∀i,0<w i) {a e b κ:ℝ} (ha:0≤a) (fund:A.Pays w a e κ)
    (extra:C.Paid (wallet R w) P.p.B a b) (t:T) (U:Config G n) (F:V→ℂ)
    (guard:C.log t U=ink R F) :
    let out:=(issued A C).density t U
    read R (fun _=>0) out=A.density t U ∧
    (∀s,(read R (fun _=>1) out).part s=(P.eval U:ℂ)*∏v∈s.val,F v) ∧
    (∀v,(read R (fun _=>2) out).part (R.fire v)=(A.density t U).part (R.fire v)-
      (P.eval U:ℂ)*F v) ∧
    ∀s,(read R (fun _=>2) out).part s=
      ∑u:R.Mode,∑v:R.Mode,if Poly.merges u v s then
        (A.density t U).part u*(∏j∈v.val,-F j) else 0 := by
  dsimp only
  rw [original A C wp ha fund extra t U F guard]
  have same:=A.same fund ha wp t U
  exact ⟨WilsonOriginalAlternativeExtraction.original R _ _,fun s=>(trial R _ _ s).trans
    (by rw [same]),fun v=>(signed R _ _ v).trans (by rw [same]),mixed R _ _⟩

end YM.Integration.WilsonOriginalAlternativeGallery

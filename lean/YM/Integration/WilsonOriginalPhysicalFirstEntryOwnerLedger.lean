import YM.Integration.WilsonSeparatedPrefixCanonicalPublicSale
import YM.Integration.WilsonSeparatedPrefixCanonicalForced
import YM.Integration.WilsonSeparatedPrefixCanonicalFares

/-! Rooted hard wages for the canonical incoming reflected experiment. The
previous mixed and quiet gas is the one returned by the original sale. Each
named increment is the grouped original forced profile of that same field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerLedger
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Ac Marker Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent Extra.Histories
open Push.GridApprox.Nil Push.Local
open scoped Classical BigOperators
section Issued
variable {G:Gauge}{m:Side}{V:Type}[Fintype V][DecidableEq V]{marks:Census V}
  {degree:V→ℕ}{labels:∀v,Labels.Frame G (degree v)}{P:Rep G m}{o:V→Site m}
  (q:∀v,Coefficient (labels v) m) (φ:V → Config G m→ℂ) (F:Config G m→Poly marks)
  (w:V→ℝ) (κ:ℝ)(B:V→ℝ)

/-- The existing mixed barcode, each new singleton at that own barcode, and
their combined site bill on the very same unnormalized original density. -/
def Priced : Prop :=
  ∃ H K, Carton o H K P.p.threshold ∧
    Towed w id H P.p.B P.p.supportExponent 1 ∧
    Towed w Prod.fst K P.p.B P.p.supportExponent 1 ∧
    F=restore P φ (fun v=>profile P.activities (q v).forced) H K ∧
    (∀v,let h:=fun b U=>Poly.send (marks.fire v) (profile P.activities (q v).forced b U)
        Towed w Prod.fst h P.p.B P.p.supportExponent (w v*(κ*B v)) ∧
        ∀b,Flow o b (h b) P.p.threshold) ∧
    Towed w Prod.fst (fun b U=>Mach marks (fun v=>profile P.activities (q v).forced b U)+K b U)
      P.p.B P.p.supportExponent (1+κ*∑v,w v*B v)

theorem filed (wp:∀v,0<w v) (expo:0≤P.p.supportExponent){A:Hol G}
    (shapes:∀v,(q v).Format (o v) A P)(fees:∀v,(q v).remBound (o v) P κ (B v))
    (admit:Served P φ (fun v=>profile P.activities (q v).forced) F o w P.p.supportExponent 1) :
    Priced (P:=P) (o:=o) q φ F w κ B :=by
  obtain ⟨H,K,rooms,green,black,correct⟩:=admit
  have single:=fun v=>WilsonSeparatedPrefixCanonicalForced.original (J:=marks) v (q v) (shapes v) w wp expo (fees v)
  refine ⟨H,K,rooms,green,black,correct,single,?_⟩
  have all:=WilsonSeparatedPrefixCanonicalFares.add_family univ (fun v _=>(single v).1) black
  have total:(∑v:V,w v*(κ*B v))+1=1+κ*∑v,w v*B v:=by
    rw [Finset.mul_sum]
    simp_rw [show ∀v:V,w v*(κ*B v)=κ*(w v*B v) from fun _=>by ring]
    ring
  rw [←total]
  exact all

theorem served (sale:Priced (P:=P) (o:=o) q φ F w κ B) :
    Served P φ (fun v=>profile P.activities (q v).forced) F o w P.p.supportExponent 1:=by
  obtain ⟨H,K,rooms,green,black,correct,_,_⟩:=sale
  exact ⟨H,K,rooms,green,black,correct⟩
end Issued
end YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerLedger

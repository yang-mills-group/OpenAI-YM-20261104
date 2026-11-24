import YM.Integration.WilsonMovingForkDatedContrast
import YM.Integration.WilsonSeparatedGridDesign

/-! The entire input product and each reflected original basis pair share
one outer column and one filed inverse. Keep their screened physical
weights in the common finite signed sum up to the terminal receiver. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.WilsonMovingForkOpticalContrast
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonMovingForkHeterogeneousCut (Invoice Filed Heard)
open WilsonMovingForkMixedSeed (doses product)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonPublicForkTrialHearing
open scoped Classical Topology BigOperators
open WilsonMovingForkDatedExterior (At)
open WilsonMovingForkShiftedSite (Reached)

open WilsonMovingForkPrintedFile (Program row)
open WilsonSeparatedBranchStencil (Trial read)
attribute [local instance] Trial.count
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{n b u v c K j:ℕ}{d:Fin b → ℕ}
    {fields:∀i,S.Field (d i)}
local notation "C" => R.family

abbrev Node {I:Type}(Y:Trial (n+1))(M:I → Trial 2):=Y.sample ⊕ (Σk,(M k).sample)

abbrev arity {I:Type}{Y:Trial (n+1)}{M:I → Trial 2}:Node Y M → ℕ
  | .inl _=>n+1
  | .inr _=>2

def nearPorts (far:Fin b)(near:Fin n → Fin b):Fin (n+1) → Fin b:=Fin.lastCases far near
def pairPorts (far head:Fin b):Fin 2 → Fin b:=Fin.cases head (fun _:Fin 1=>far)

def ports {I:Type}{Y:Trial (n+1)}{M:I → Trial 2}(far:Fin b)(near:Fin n → Fin b)(head:I→Fin b):
    (a:Node Y M)→Fin (arity a)→Fin b
  | .inl _=>nearPorts far near
  | .inr ⟨k,_⟩=>pairPorts far (head k)

def weight {I:Type}(Y:Trial (n+1))(M:I → Trial 2)(c:I → ℂ):Node Y M → ℂ
  | .inl a=>(Y.weight a:ℂ)
  | .inr ⟨k,a⟩=> -c k*(M k).weight a

def point {I:Type}(Y:Trial (n+1))(M:I → Trial 2):(a:Node Y M) → Points (arity a)
  | .inl a=>Y.site a
  | .inr ⟨k,a⟩=>(M k).site a

def active (r:ℝ){s:ℕ}(pick:Fin s→Fin b)(x:Points s):ℂ:=
  S.classMoment S (fun i=>d (pick i)) (r • x) (fun i=>fields (pick i))

include F in
theorem original (order:(l:Filter _)≤f.fuse)(jK:j≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K)
    (master:Filed R d K)(arms:∀i,Arm (C) S (l:Filter _) (d i) (fields i))
    {I:Type}[Fintype I](Y:Trial (n+1))(M:I → Trial 2)(far:Fin b)(near:Fin n→Fin b)(head:I→Fin b)
    (r:ℝ)(coef:I→ℂ)(prog:∀a:Node Y M,Program R (fun i=>d (ports far near head a i)) K)
    (actual offered:∀a:Node Y M,Fin (arity a) → Cover)
    (located:∀a,tag ((C).S.a j) (actual a)=r • point Y M a)
    (generic:∀a,tag ((C).S.a j) (actual a)∈generic (arity a))
    (phase:Node Y M→ℝ)(wallet:Node Y M→Invoice)(terminal:Node Y M → (ℕ×ℕ)→ℂ)(tail:ℝ)
    (placed:∀a,Reached (R:=R) (fun i=>arms (ports far near head a i)) jK uv vc ck (actual a) (offered a) (phase a))
    (paid:∀ᶠz:ℕ×ℕ in f.fuse,∀top:K<z.1,∀a,At (WilsonMovingForkDatedContrast.face master
      (ports far near head a) (prog a)) uv vc ck jK (offered a) z top
        (fun i=>(arms (ports far near head a i)).source z) (terminal a z) (wallet a))
    (combined:∀ᶠz:ℕ×ℕ in f.fuse,‖∑a,weight Y M coef a*terminal a z‖≤tail):
    ‖read Y (active (fields:=fields) r (nearPorts far near))-
      ∑k,coef k*read (M k) (active (fields:=fields) r (pairPorts far (head k)))‖≤
       (∑a,‖weight Y M coef a‖*(phase a+(wallet a).total v c K))+tail:=by
  have fee:=WilsonMovingForkDatedContrast.original F arms master order jK uv vc ck (I:=Node Y M) arity
    (ports far near head) prog actual offered generic (weight Y M coef) phase wallet terminal tail placed paid combined
  have form:(∑a:Node Y M,weight Y M coef a*S.classMoment S (fun i=>d (ports far near head a i))
    (tag ((C).S.a j) (actual a)) (fun i=>fields (ports far near head a i)))=
      read Y (active (fields:=fields) r (nearPorts far near))-
        ∑k,coef k*read (M k) (active (fields:=fields) r (pairPorts far (head k))):=by
    simp_rw [located]
    rw [Fintype.sum_sum_type,Fintype.sum_sigma]
    change (∑a:Y.sample,(Y.weight a:ℂ)*active (fields:=fields) r (nearPorts far near) (Y.site a))+
      (∑k,∑a:(M k).sample,(-coef k*((M k).weight a:ℂ))*active (fields:=fields) r (pairPorts far (head k)) ((M k).site a))=_
    simp only [WilsonSeparatedBranchStencil.read,Complex.real_smul,Finset.mul_sum,neg_mul,mul_assoc,Finset.sum_neg_distrib,sub_eq_add_neg]
  exact form ▸ fee

end YM.Integration.WilsonMovingForkOpticalContrast
end

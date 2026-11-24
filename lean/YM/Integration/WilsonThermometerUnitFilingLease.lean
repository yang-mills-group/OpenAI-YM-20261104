import YM.Integration.WilsonOlderFreshGraphStrip
import YM.Integration.WilsonThermometerUnitFilingTuition

/-! A second native set of teacher roots for the older signed ordinary field, selected on the public prelength sheet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingLease
open Function Finset Lattice RG RG.Supply Wilson Precision Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Next.Foundations Push.PriceCompiler
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent
open WilsonOriginalCompoundStrip WilsonThermometerUnitFilingCampus
open scoped Classical BigOperators
variable {G:Gauge}
abbrev Rooms (k:ℕ):=Fin (k+2)×Fin 2

def strip (X:Request G)(K:KernelChoices)(x k:ℕ)(c:Rooms k):ℝ:=width X K (x-c.2.val) c.1

theorem strip_pos (X:Request G)(K:KernelChoices)(x k:ℕ)(c:Rooms k):
    0<strip X K x k c:=lt_min one_pos (div_pos (X.positive ..) (mul_pos (by norm_num) (X.grows _)))

def common (X:Request G)(K:KernelChoices)(k x:ℕ):ℝ:=
  (1+∑c:Rooms k,(strip X K x k c)⁻¹)⁻¹

theorem rooms (X:Request G)(K:KernelChoices)(k x:ℕ):
    0<common X K k x ∧ ∀c, common X K k x ≤ strip X K x k c:=by
  have poss(c:Rooms k):0<(strip X K x k c)⁻¹:=inv_pos.mpr (strip_pos ..)
  have nn:0≤∑c:Rooms k,(strip X K x k c)⁻¹:=sum_nonneg (fun c _=>(poss c).le)
  refine ⟨inv_pos.mpr (by linarith),?_⟩
  intro c
  have hit:(strip X K x k c)⁻¹≤∑z:Rooms k,(strip X K x k z)⁻¹:=single_le_sum (fun z _=>(poss z).le) (mem_univ c)
  exact (inv_anti₀ (poss c) (show (strip X K x k c)⁻¹≤1+∑z:Rooms k,(strip X K x k z)⁻¹ by linarith)).trans (inv_inv _).le

private def contract (X:Request G)(simple:G.Simple)(A:ℕ→Stage)(pr:MapPrices)(K:KernelChoices):
    PlanV.Roots (G:=G) A pr K:=
  WilsonOlderFreshGraphStrip.roots simple A pr K (common X K) (fun _=>1)
    (fun k x=>(rooms X K k x).1) (fun _=>one_pos)

def roots (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices):
    PlanV.Roots (G:=G) s.profile pr s.kernel:=
  contract (syllabus Q simple φ s pr) simple s.profile pr s.kernel

theorem raised (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices)(l:ℕ→ℕ):
    roots Q simple φ (ThroughLaunch.raise s l) pr=roots Q simple φ s pr:=by
  apply congrArg (fun X=>contract X simple s.profile pr s.kernel)
  rfl

theorem smaller (Q:Request G)(simple:G.Simple)(φ:ℕ→ℕ→ℕ)(s:Sheet G)(pr:MapPrices)
    (ψ:ℕ→ℕ)(k x:ℕ)(working:1≤k)(c:Rooms k):
    Poetry.Agenda.seed (roots Q simple φ s pr) ψ k x ≤ width (syllabus Q simple φ s pr) s.kernel (x-c.2) c.1:=by
  let X:=syllabus Q simple φ s pr
  have paid:=WilsonOlderFreshGraphStrip.narrow simple s.profile pr s.kernel (common X s.kernel) (fun _=>1)
    (fun l y=>(rooms X s.kernel l y).1) (fun _=>one_pos) ψ k x working
  exact paid.trans ((div_le_self (rooms X s.kernel k x).1.le (by norm_num)).trans ((rooms X s.kernel k x).2 c))

theorem original (Q:Request G)(R:Run G)(simple:G.Simple)
    (paid:WilsonThermometerUnitFilingCampus.Invoice Q simple (fun _=>MintClock.splits) R.kit)
    (ψ:ℕ→ℕ)(i H p k:ℕ)(fit:H≤R.alloy.B.a.clock.J i)(work:1≤k)(enough:H≤k+1)
    (born:p≤R.alloy.B.a.clock.J i+1):
    let A:=R.alloy.B.a
    let X:=WilsonThermometerUnitFilingTuition.elected Q R simple
    let μ:=width X R.metals.p.kernel (A.clock.J i) H
    let old:=roots Q simple (fun _=>MintClock.splits) R.metals.p R.metals.K
    let σ:=Poetry.Agenda.seed old ψ k (A.clock.J (i+1))
    let rawWidth:=Poetry.Agenda.seed (WilsonWindowRootPurchase.roots simple R.metals.p R.metals.K)
      MintClock.splits (Burn.horizon p) (A.clock.J (i+1))
    0<σ ∧ σ≤μ ∧ σ≤rawWidth/(16*max 1 (Q.multiplier H)) ∧ σ≤rawWidth:=by
  intro A X μ old σ rawWidth
  let j:=A.clock.J i
  let x:=A.clock.J (i+1)
  have low:j≤x:=A.fits.mono (Nat.le_succ i)
  have high:x≤j+1:=A.fits.stepSlow i
  let c:Rooms k:=(⟨H,by omega⟩,⟨x-j,by omega⟩)
  have fin:σ≤width X R.metals.p.kernel (x-(x-j)) H:=smaller Q simple (fun _=>MintClock.splits)
    R.metals.p R.metals.K ψ k x work c
  have ix:x-(x-j)=j:=by omega
  rw [ix] at fin
  have donor:=WilsonThermometerUnitFilingTuition.adjacent Q R simple paid i H p fit born
  exact ⟨Poetry.Agenda.stem ..,fin,fin.trans donor.2.1,fin.trans donor.2.2⟩

end YM.Integration.WilsonThermometerUnitFilingLease

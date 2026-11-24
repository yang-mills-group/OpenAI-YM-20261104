import YM.Integration.WilsonRootedKioskOriginalPermit
import YM.Integration.WilsonRootedKioskFieldPost

/-! The twice merged physical Semester pays its whole independent subtraction
and retains the genuine quiet density on every original field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedKioskOriginalPost
open Lattice Ac RG Wilson Marker QuadraticLocal Push.AbsoluteSums WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {V T I:Type}[DecidableEq V]{R:Census V}{G:Gauge}{n:Side}{P:BudgetPoint}
  {o:V→Site n}{B:ℕ}{upper lower fee:ℝ}{w:V→ℝ}

theorem weaken (L:Lamps T I G P o R) (positive:∀v,0<w v) (order:lower≤upper)
    (paid:Gross L w B upper fee):Gross L w B lower fee:=by
  obtain ⟨f,fp,read,bill⟩:=paid.before
  have toll (mode:R.Mode):0≤Poly.toll w mode:=Finset.prod_nonneg fun v _=>(positive v).le
  refine ⟨f,fp,read,fun x=>budget_mono (bill x) ?_ ?_⟩
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (toll _) (fp i)) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i
    split
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (toll _) (fp i))
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right order (Nat.cast_nonneg _))
    · exact le_rfl
end YM.Integration.WilsonRootedKioskOriginalPost
namespace YM.QuadraticLocal.Tint
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Ink
open Push.SectorMeasure ConnectedActivityE6 RemainderComparison Trigger Patrol
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι J: Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e r b k τ ε δ :ℝ}
variable (X:ι→Row P R G α)
open Travel Club Typeface Lyric
variable {U:RG.Rep G n} {R':Rep G c} (T:Incoming P U α J R) (w:V→ℝ) (tV:V→ℕ)
open Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Pressure
namespace Institute
open Lotus Merge Campus Hearth
local notation "Y"=> Patrol.picture X T
variable (hq:HasSlots U.p U.activities)[Countable ι][Countable J]
variable (y:α)
variable {D:Teller G}{W:ConnectedActivityE6.Target G D} {L:Side} {S:StepData c n} {A:Tube G S} {F:ConnectedActivityE6.Target.Order G a}
variable (H:Cash a e k L W F τ A U)
variable {P':Burn.Locale G} (M0:Burn.Seed U P') (hβ: U.p.B≤2*radiusB e)
variable {χ d d' V₁ V₂ B₀ b₁ χ' v' uA uB tW:ℝ}
variable (E:Earnings) (Q:Eyes H R' χ d d' 16 E.count)
local notation "Hp"=> E.top
variable (D0:ℕ) (Kc: Campus.Batch X→ℕ)
local notation "X0"=> E.helmet
local notation "j"=> E.cause
local notation "κ"=> (E.count)
local notation "s_1"=> E.stage
local notation "ξ"=> E.before
local notation "ρ"=> E.afterwards
local notation "ψ"=> E.rank
local notation "η"=> E.width
local notation "µ"=> (S.ratio.count)
local notation "Go"=> (Coat.gStep U.beta)

variable (S':Press X E.cause) (hS:Press.Receipt X S' E.width E.merchant) (Yv: Width.Viewer X S' E.width U.p.B)
local notation "s₂"=> (U.p.B)
local notation "T!"=> R'.p.supportExponent+1+1

variable (k':ℝ) (hV:Scene.Armada X w tV E.before b E.cause E.count E.rank)
variable (hP:E.Valid G S.ratio.count U.p R'.p b (Coat.gStep U.beta) k' tW) (hr0:0<ε) (hr1:ε≤1)
variable (hl: T.old.Paid w U.p.B U.p.supportExponent ε) (hh:T.hard.Paid w U.p.B U.p.supportExponent 1)
local notation "hw"=> hV.positive
local notation "X_"=> (P.coarser S.ratio).origin
local notation "z_"=> (U.p).supportExponent
variable (hK:Grammar H M0 E Q E.helmet D0 δ)
variable (Y0:Institute.Permit (R':=R') (ε:=ε) (δ:=δ) X T w tV hq y H M0 hβ E D0 S' Yv hV)
namespace Permit
local notation "Fp"=> (Width.treasured X S.ratio S' hS R'.p E.afterwards Go)
local notation "ϕ"=> (fun z:Club X=> (Club.cardLe X z).trans (hV.quota (Club.alliance X z)))
local notation "Kp" => Y0.book
local notation "π"=> Y0.pick
local notation "ℓ"=> E.fail ε δ Go
local notation "Q*"=> Y0.semester
local notation "z"=> (show 2*((2:ℝ)+1) ≤ 16 from by norm_num)
local notation "ι₀"=> (d'^E.count*d)
local notation "χ1"=> E.hitPrice G µ U.p R'.p b ε δ Go
local notation "μ"=> E.grow G µ R'.p b
local notation "ς"=> E.miss G µ U.p R'.p b
local notation "ρE"=> E.pay µ R'.p b
open Week.Semester
local notation "θ"=> (R'.p.supportExponent+1+1)
local notation "Qb"=> R'.p.B
variable (uV: Travel.Walk H R' χ uA uB tW)
local notation "E★"=> (Curtain.ledger X T w hw hq Kp y H Hp D0 M0 hβ ℓ π Y0.budget S' Yv X0 Q* hP.location hS E.afterwards)

open Integration
local notation "Sp"=> (Curtain.sprout X T w hw hq Kp y H Hp D0 M0 hβ Q π z ϕ S' Yv X0 hK.edges Q* hP.location hS E.afterwards)
local notation "incoming"=> (Travel.raw H Q (Patrol.picture X T) w Kp hw hq z y)
local notation "shiftPrice"=> (Shelter.Deck.crewCost X0 (R'.p.supportExponent+1) E.bearing*(ι₀+μ+ρE))
local notation "grossPrice"=> ((Spill.allOver R'.p)^E.cap*(E.grow G µ R'.p b))


local notation "firstRead"=> (Travel.mid H uV Q (Patrol.picture X T) w Kp hw hq hV.quota z y)

include hl
theorem occupied_reclosure [Fintype V] (field:R'.eval=S.push U.beta U.eval)
    (positive:∀v,R'.eval v≠0) (sp:0<tW) (extra:ℝ) (forest:Tree.Forest S.ratio):
    letI:=Scene.crewC X S.ratio S' hS
    let radius:=WilsonRootedKioskFreeRadius.radius extra shiftPrice grossPrice tW
    let gallery:=WilsonRootedKioskPostedPortfolio.residual firstRead uV.second (Fp) (E★) (Sp)
    1≤radius ∧ extra≤radius ∧ gallery.Pays (Stoop.radius w radius) R'.p.supportExponent (radius⁻¹*χ1) uB ∧
      (∀t v,gallery.density t v=Poly.pass (-(WilsonRootedKioskOccupiedSlip.bare (Fp) t v))*
        S.push U.beta ((Patrol.picture X T).density t) v) ∧
      ∀t v,(gallery.density t v).part R.quiet=(R'.eval v:ℂ):=by
  haveI:=Scene.crewC X S.ratio S' hS
  have bank:=Permit.occupied_inputs (X:=X) (T:=T) (w:=w) (tV:=tV) (hq:=hq) (y:=y) (H:=H) (M0:=M0) (hβ:=hβ)
    (E:=E) (Q:=Q) (D0:=D0) (S':=S') (hS:=hS) (Yv:=Yv) (k':=k') (hV:=hV) (hP:=hP) (hK:=hK) (hl:=hl) (Y0:=Y0) (uV:=uV)
  have openBill:=WilsonRootedKioskOriginalPost.weaken (Fp) hw (show R'.p.supportExponent+1≤θ by linarith) bank.2.2.1
  have regular:=(E★).tenure w hw bank.2.1 (show R'.p.supportExponent≤θ by linarith)
  exact WilsonRootedKioskFieldPost.original H Q uV (Patrol.picture X T) w Kp hw hq hV.quota z y (Fp) (E★) (Sp)
    field positive regular bank.1 openBill sp extra bank.2.2.2 forest

end Permit
end Institute
end YM.QuadraticLocal.Tint

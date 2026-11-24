import YM.QuadraticLocal.Campaign.Homes
import YM.Integration.WilsonRootedKioskOriginalPost
import YM.Integration.WilsonMixedFreshMergerCrown

/-! A fresh physical insertion on the same elected Wilson second merger as the old signed return. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalSignedFreshPermit
open Lattice Wilson RG Marker QuadraticLocal WilsonRootedKioskOccupiedSlip
open scoped Classical
variable {G:Gauge} {n:Side} {I V T:Type} [DecidableEq V] {R:Census V}
  {p:BudgetPoint} {o:V→Site n} (L:Lamps T I G p o R)

theorem shade_bare (t:T) (U:Config G n) :
    bare L.shade t U = -bare L t U := by
  unfold WilsonRootedKioskOccupiedSlip.bare
  rw [←tsum_neg]
  apply tsum_congr
  intro i
  ext m
  simp only [Lamps.shade,Pi.neg_apply,Poly.part_send,Poly.part_neg]
  split <;> simp

theorem shade_gross {w:V→ℝ} {B:ℕ} {a c:ℝ} (h:Gross L w B a c) :
    Gross L.shade w B a c := by
  obtain ⟨f,pos,values,hit⟩:=h.before
  exact ⟨f,pos,fun i t U=>by simpa only [Lamps.shade,Pi.neg_apply,norm_neg] using values i t U,hit⟩

theorem phase_add {u f debt shift b opp total core e : Poly R}
    (source:u=f+debt+shift) (minus:opp= -b) (add:total=b+core)
    (old:core=f+e) (same:e=debt) : u=opp+total+shift := by
  rw [source,minus,add,old,same]
  abel

end YM.Integration.WilsonOriginalSignedFreshPermit
namespace YM.QuadraticLocal.Tint
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Ink
open Push.SectorMeasure ConnectedActivityE6 RemainderComparison Trigger Patrol
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V ι J: Type}[DecidableEq V][Fintype V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e r b k τ ε δ :ℝ}
variable {Film:V→Type} [∀ v,AddCommGroup (Film v)] [∀ v, Module ℝ (Film v)]
variable (actors:∀ v, Set (Film v)) (pieces:∀ v,Submodule ℝ (Film v))
variable (X:ι→Row P R G (Affinity.Wallet actors))
open Travel Club Typeface Lyric
variable {U:RG.Rep G n} {R':Rep G c} (T:Incoming P U (Affinity.Wallet actors) J R) (w:V→ℝ) (tV:V→ℕ)
open Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Pressure
namespace Institute
open Lotus Merge Campus Hearth
local notation "Y"=> Patrol.picture X T
variable (hq:HasSlots U.p U.activities)[Countable ι][Countable J]
variable (y:Affinity.Wallet actors)
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


open Affinity
local notation "ν"=> Curtain.Ceremony.Senior actors X T w hw hq Kp y H Hp D0 M0 hβ ℓ π Y0.budget S' Yv X0 Q* hP.location hS ρ
local notation "err" hx:max ht:max hf:max=> Curtain.Ceremony.reveled actors pieces X T w hw hq Kp y H Hp D0 M0 hβ Q ℓ π z ϕ Y0.budget S' Yv X0 Q* hP.location hS ρ hx ht hf
local notation "σ"=> (P.coarser S.ratio)
variable {I:Type} [Countable I]
variable (bornRow:Lamps (Affinity.Wallet actors) I G R'.p (S.ratio.parent ∘ P.origin) R)

include hl in
theorem received_birth (hX:Earn.Tableau pieces actors X)
    (hΛ:Taut P.support actors pieces T.old) (htF:Crown P.support actors pieces T.hard) (field:R'.eval=S.push U.beta U.eval) (positive:∀v,R'.eval v≠0)
    {regular gross : ℝ} (paid:bornRow.Paid w Qb θ regular)
    (all:WilsonRootedKioskOccupiedSlip.Gross bornRow w Qb (R'.p.supportExponent+1) gross)
    (file:Taut (σ).support actors pieces bornRow) (slack:0<tW) (extra:ℝ) (forest:Tree.Forest S.ratio) :
    letI := Scene.crewC X S.ratio S' hS
    let h := WilsonRootedKioskFreeRadius.radius extra shiftPrice gross tW
    let changed := Kiosk.Second.canopy firstRead (WilsonRootedKioskSlipCharge.roll (Sp) bornRow.shade) uV.second
    let next : Incoming (σ) R' (Affinity.Wallet actors) _ R := ⟨err hX hΛ htF,changed⟩
    1≤h ∧ extra≤h ∧
      next.old.Paid w Qb θ χ1 ∧ next.hard.Paid (Stoop.radius w h) Qb R'.p.supportExponent uB ∧
      Taut (σ).support actors pieces next.old ∧ Crown (σ).support actors pieces next.hard ∧
      let view : Gallery (Affinity.Wallet actors) _ (σ).origin R' R := ⟨bornRow.join ((Fp).join next.old),next.hard⟩
      (∀ t v, view.density t v=Poly.pass (WilsonRootedKioskOccupiedSlip.bare bornRow t v)*
          S.push U.beta ((Patrol.picture X T).density t) v) ∧
      ∀ t v,(view.density t v).part R.quiet=(R'.eval v:ℂ) := by
  letI := Scene.crewC X S.ratio S' hS
  have bank := Permit.occupied_inputs (X:=X) (T:=T) (w:=w) (tV:=tV) (hq:=hq) (y:=y) (H:=H)
    (M0:=M0) (hβ:=hβ) (E:=E) (Q:=Q) (D0:=D0) (S':=S') (hS:=hS) (Yv:=Yv) (k':=k')
    (hV:=hV) (hP:=hP) (hK:=hK) (hl:=hl) (Y0:=Y0) (uV:=uV)
  have energy := Permit.energy X T w tV hq y H M0 hβ E Q D0 S' hS Yv k' hV hP hK Y0 uV
  let safe := Curtain.Ceremony.enchanted actors pieces X T w hw hq Kp y H Hp D0 M0 hβ Q ℓ π z ϕ Y0.budget
    S' Yv X0 Q* hP.location hS ρ hX hΛ htF
  have toll : ((err hX hΛ htF)).Paid w Qb θ χ1 := Polish.costs actors pieces (E★) (σ).support safe bank.2.1
  have old := Lamps.joinPaid energy.1 toll
  have low : R'.p.supportExponent≤θ := by linarith
  have funded := Lamps.joinPaid (bornRow.tenure w hw paid low) (((Fp).join ((err hX hΛ htF))).tenure w hw old low)
  have θ₀ : 0≤θ := by linarith [R'.p.exponent_pos]
  have phase (t : Affinity.Wallet actors) (v : Config G c) :
      (incoming).log t v=bornRow.shade.log t v+(bornRow.join ((Fp).join ((err hX hΛ htF)))).log t v+(Sp).log t v := by
    have reprinted : (err hX hΛ htF).log t v=(E★).log t v :=
      Polish.stems actors pieces (E★) (σ).support safe t v
    exact WilsonOriginalSignedFreshPermit.phase_add (bank.2.2.2 t v) (Lamps.shade_log bornRow t v)
      (Lamps.joinLog t v (paid.sums θ₀ hw ..) (old.sums θ₀ hw ..))
      (Lamps.joinLog t v (energy.1.sums θ₀ hw ..) (toll.sums θ₀ hw ..)) reprinted
  have outcome := WilsonRootedKioskFieldPost.original H Q uV (Patrol.picture X T) w Kp hw hq hV.quota z y
    bornRow.shade (bornRow.join ((Fp).join ((err hX hΛ htF)))) (Sp) field positive funded bank.1
    (WilsonOriginalSignedFreshPermit.shade_gross bornRow all) slack extra phase forest
  have pres := Travel.Cabin.attentive H uV Q actors pieces (Patrol.picture X T) w Kp hw hq hV.quota z y P.support
    (Curtain.Ceremony.spied actors pieces X T w hw hq H Q z ϕ hX hΛ htF)
  have store := Polish.tenancy actors pieces (E★) (σ).support safe
  have tags := WilsonMixedFreshMergerCrown.posted actors pieces (σ).support firstRead uV.second
    ((Fp).join ((err hX hΛ htF))) bornRow (Sp) pres (Polish.Static.spawn (hX.formal S.ratio S' hS ρ R'.p Go) store) file
    (fun i v=>Curtain.Ceremony.soaps actors pieces X T w hw hq Kp y H Hp D0 M0 hβ Q π z ϕ S' Yv X0
      hK.edges Q* hP.location hS ρ v hX hΛ htF i)
  exact ⟨outcome.1,outcome.2.1,toll,outcome.2.2.1.wages,store,tags.hard,
    fun t v=>by
      have row := outcome.2.2.2.1 t v
      rw [WilsonOriginalSignedFreshPermit.shade_bare,neg_neg] at row
      exact row,
    outcome.2.2.2.2⟩
end Permit
end Institute
end YM.QuadraticLocal.Tint

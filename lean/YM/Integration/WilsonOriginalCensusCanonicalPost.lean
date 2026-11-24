import YM.Integration.WilsonOriginalCensusCanonicalRows
import YM.Integration.WilsonOriginalFreshCensusPost
import YM.Next.WARD_BIN.Lambda

/-! Canonical cut-off stencils in a fresh post on the original Wilson density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalPost
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  {V:Type}[Fintype V][DecidableEq V](d:V→ℕ)(q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
  (o:V→Site (R.family.side (i+1) per))(order shelf:ℕ)

local notation "H" => Ψ (i+1)
local notation "scale" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M" => row R d q hd o scale
local notation "A" => room V
local notation "K₀" => (fun _:V=>(⊥:Submodule ℝ ℂ))
local notation "marks" => Stock.census V
local notation "w₀" => (fun _:V=>(1:ℝ))
local notation "C₀" => charge R d q scale w₀
local notation "g" => Coat.gStep (H).beta
local notation "D₀" => (∑v:V,d v)+1
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "physical" => fun (x:Wallet (A))(U:Config G (R.family.side (i+1) per))=>
  ((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) x U)
local notation "Ptype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (A) (K₀)
  d order shelf op.count i hi (physical)

/- The original post is selected before the direction and every occupied face.
Its enrollment retains each compulsory key in the original hard register. -/
include simple course cut cal hospital chamber in
theorem original
    (fit:∀j,rank R d (entry R d j (q j)) ≤ order)(slots:Fintype.card V ≤ op.count)
    (space:∑j,d j ≤ shelf)(level:shelf ≤ R.alloy.B.a.clock.J i)
    (ord:order ≤ R.alloy.B.a.clock.J i)(stage:order+1 ≤ op.stage)
    (count:op.count ≤ Burn.horizon k+2)(cap:order+(∑j,d j) ≤ Burn.horizon k+2)
    {tol:ℝ}(tp:0 < tol)(x₀:Wallet (A))
    (atBare:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(pass:Pass D Q R.alloy R.kit)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ i+1)
    (onset:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i):
    ∃F:Ptype,F.passport=Passport.point o ∧ F.inputIndex=Empty ∧ F.op=op ∧ F.lesson=lesson ∧
      F.modelIndex=V ∧ HEq F.model M ∧
      F.input.hard.Paid F.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      8*(budgetR R i)^op.count*F.rent ≤ tol ∧
      (∀j,(F.w j)⁻¹ ≤ max 1 (C₀)*(χ+2^(order+shelf+1+(D₀))*χ^((D₀)+2))) ∧
      (∀x,(Tint.Patrol.picture F.model F.input).density x=(physical) x) ∧
      ∀{h:V→ℕ}(κ:(j:V)→Knob (h j))(pt:V→Chamber)(x:Wallet (A))
        (U:Config G (R.family.side (i+1) per))(s:(marks).Mode),
        (((Tint.Patrol.picture F.model F.input).density x U).part s)/((H).eval U:ℂ)=
          ∏j∈s.val,probe j x*WilsonReceivedCanonicalVerseBasis.restored R d κ pt
            (regulatorRun R.family N per (i+1)) j (q j) (o j) U:=by
  have stock:=WilsonOriginalCensusCanonicalRows.fleet R d q hd o scale w₀ (fun _=>zero_lt_one)
    order op.count shelf fit slots space
  have voter:Mentor.Cruise.Voter M scale order op.count op.stage k (R.alloy.B.a.clock.J i):=by
    refine ⟨fun j=>?_,fun s=>s.val.card_le_univ.trans slots,stage,fun s=>?_⟩
    · have inc:d j ≤ ∑v,d v:=single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ j)
      exact ⟨stock.honor j,stock.purchases.1 j,(Nat.sub_le _ _).trans ((fit j).trans ord),
        inc.trans (space.trans level)⟩
    · rw [Press.tall _ s d stock.purchases.2]
      exact (Nat.add_le_add_left (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)) order).trans cap
  have cp:0 ≤ C₀:=sum_nonneg fun j _=>mul_nonneg zero_le_one (WilsonOriginalCensusCanonicalRows.nonneg ..)
  have nxt:=R.alloy.B.a.fits.mono (Nat.le_succ i)
  obtain ⟨F,placed,empty,event,weather,names,ink,hard,rental,_,fee,law⟩:=
    WilsonOriginalFreshCensusPost.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson
      cal ahead chamber hospital (Passport.point o) (A) (K₀) M w₀ d order shelf voter count level
      (ord.trans nxt) cp tp stock (tested R d q hd o scale) x₀ atBare warm pass halo onset
  refine ⟨F,placed,empty,event,weather,names,ink,hard,rental,?_,law,?_⟩
  · intro j
    simpa only [inv_one,one_mul] using fee j
  · intro h κ pt x U s
    rw [law]
    have entryβ:regulatorRun R.family N per (i+1)=(g):=by
      rw [(course.1.walk (i+1) (by omega) (by omega)).beta]
      rfl
    have same:(H).eval=(R.family.path.rep N per (i+1)).eval:=(course.1.walk (i+1) (by omega) (by omega)).view
    have heat:((H).eval U)≠0:=by
      rw [same]
      exact (Multi.AxisShift.chosen_positive R.makes.wilson (p:=per) (show i+1 ≤ N by omega) U).ne'
    rw [entryβ]
    have source:Spill.Foundry.uncut M (g) x U=∑j,WardBin.Lambda.fuse j
        (probe j x*WilsonReceivedCanonicalVerseBasis.restored R d κ pt (g) j (q j) (o j) U):=by
      unfold Spill.Foundry.uncut
      rw [tsum_fintype]
      refine sum_congr rfl (fun j _=>?_)
      change Poly.send ((marks).fire j) ((M j).nominal (g) x U)=_
      rw [WilsonOriginalCensusCanonicalRows.nominal R d q hd o scale κ pt]
      rfl
    change ((((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) x U)).part s)/((H).eval U:ℂ)=_
    rw [source,Poly.part_smul,WardBin.Lambda.passion,WardBin.Lambda.expend]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr heat)

end YM.Integration.WilsonOriginalCensusCanonicalPost
end

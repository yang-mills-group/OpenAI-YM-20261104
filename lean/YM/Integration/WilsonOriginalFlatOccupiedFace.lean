import YM.Integration.WilsonFullFaceSignedHard
import YM.Integration.WilsonOriginalFlatHaloRate

/-! Withdraw the complete occupied part of an ordinary face on the original
older Wilson law, with the exact exclusions and the connected or disjoint
quiet partners of every occupied owner. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFlatOccupiedFace
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open scoped BigOperators Classical


open Extra.Histories Planned.GuardedAtom
open WilsonCenteredMaskPieces WilsonCenteredSoftInventory WilsonCenteredOccupiedHardSets
open WilsonCenteredMixedSetFiling WilsonCenteredCompleteGallery
open WilsonFullFaceSignedHard
open private YM.Push.RelayDifference.mark_sub from YM.Push.RELAY_DIFFERENCE.Subtraction

section Components
variable {G:Gauge}{n:Side}{P:Rep G n}{d:ℕ}{F:Frame G d}{Y:Hol G}{y:Site n}
    {κ σ C Λ δ v:ℝ}

private theorem empty (div:0<κ):Owned (F:=F) P Y y κ 0 0:=by
  refine ⟨Extra.Histories.primary y 0,Extra.Histories.primary_format 0,
    Extra.Histories.primary_rem 0 div,fun U=>?_⟩
  simp [WilsonMeasuredCoefficientTransport.account,Coefficient.marked,Extra.Histories.primary]

private theorem subtract (law:P.Lawful σ C Λ δ v){a b:ℝ}{x z:Config G n→ℂ}
    (X:Owned (F:=F) P Y y κ a x)(Z:Owned (F:=F) P Y y κ b z):
    Owned (F:=F) P Y y κ (a+b) (x-z):=by
  obtain ⟨r,valid,paid,field⟩:=X
  obtain ⟨r',valid',paid',field'⟩:=Z
  refine ⟨Push.RelayDifference.combine r r',Push.RelayDifference.combo_format valid valid',
    Push.RelayDifference.combo_cap valid valid' paid paid',fun U=>?_⟩
  change WilsonMeasuredCoefficientTransport.account _ P U=x U-z U
  rw [←field U,←field' U]
  simp only [WilsonMeasuredCoefficientTransport.account,YM.Push.RelayDifference.mark_sub]
  rw [Summable.tsum_sub ((Coefficient.marked_series law paid).summable U)
    ((Coefficient.marked_series law paid').summable U),mul_sub]

private theorem collect {I:Type}(parts:Finset I)(law:P.Lawful σ C Λ δ v)(div:0<κ)
    (bill:I→ℝ)(value:I → Config G n → ℂ)(mounted:∀z∈parts,Owned (F:=F) P Y y κ (bill z) (value z)):
    Owned (F:=F) P Y y κ (∑z∈parts,bill z) (fun U=>∑z∈parts,value z U):=by
  induction parts using Finset.induction_on with
  | empty=>
    obtain ⟨q,fit,cap,field⟩:=empty (P:=P) (F:=F) (Y:=Y) (y:=y) div
    exact ⟨q,fit,by simpa only [sum_empty] using cap,fun U=>by simpa only [sum_empty,Pi.zero_apply] using field U⟩
  | insert z parts fresh ih=>
    have left:=mounted z (mem_insert_self ..)
    have rest:=ih (fun a ha=>mounted a (mem_insert_of_mem ha))
    have joined:=subtract law left (subtract law (empty div) rest)
    simpa only [zero_add,zero_sub,sub_neg_eq_add,sum_insert fresh,Pi.add_def] using joined

variable {V X ι:Type}[DecidableEq V][Fintype V]{J:Census V}{o:V→Site n}

theorem owned [Countable ι] (A : Gallery X ι o P J) (x : X) (s : J.Mode)
    (Y : Hol G) (Z : Support n) (y : Site n)
    (center : y∈Z) (resident : ∀j∈s.val,o j∈Z)
    (K : Guard.Keeper P.p P.activities) (w : V→ℝ) (hw : ∀v,0<w v) {σ C Λ δ v κ ε E : ℝ}
    (law : P.Lawful σ C Λ δ v) (hv : 0≤v) (room : hitWidth P.p*v≤1) (div : 0<κ)
    (regular : A.E.Paid w P.p.B (P.p.supportExponent+2) E)
    (paid : A.K.Paid w P.p.B P.p.supportExponent ε) :
    Owned (F:=F) P Y y κ (fee P.p Z w s E ε v κ)
      (fun U=>(A.density x U).part s-(P.eval U:ℂ)*soft A x s U) :=by
  have old := Hard.packet_summing A.K paid P.p.exponent_pos.le hw x
  let rows (t:J.Mode) := WilsonCapturedPrimarySoftInventory.fare P.p Z w E t
  let cost (z:J.Mode×J.Mode) := (1+hitWidth P.p*v)*price (rows z.1) w z.2 ε / κ
  have face (z : J.Mode×J.Mode) (relevant : z∈occupied s) : Owned (F:=F) P Y y κ (cost z) (share A x z) :=by
    obtain ⟨present,live⟩:=mem_filter.mp relevant
    have census:=valid present
    have left : z.1.val⊆s.val:=census.2 ▸ subset_union_left
    have right : z.2.val⊆s.val:=census.2 ▸ subset_union_right
    let e := (WilsonCapturedPrimarySoftInventory.original A.E x z.1 Z
      (fun j hj=>resident j (left hj)) w hw regular).some
    letI : Countable e.Row := e.counted
    letI := Encodable.ofCountable ((e.Row×Chosen)×Finset ℕ)
    let serial : (e.Row×Chosen)×Finset ℕ ↪ ℕ := ⟨Encodable.encode,Encodable.encode_injective⟩
    obtain ⟨format,charge⟩:=WilsonCenteredMixedSetFiling.original e A.K K z.2 x y center
      (fun j hj=>resident j (right hj)) serial law.labels.forced w hw paid law.labels.boundK hv room
    obtain ⟨q,fit,bill,field⟩:=WilsonReceivedQuietCrownOwner.mounted (F:=F) Y y div _ format charge
    exact ⟨q,fit,by simpa only [cost,rows,add_mul,one_mul] using bill,fun U=>
      (field U).trans (congrArg (fun t=>(Real.exp (P.exponent U):ℂ)*t)
        (WilsonCenteredMixedSetRead.grouped e A.K K z.2 live x U serial charge law.labels.boundK (old U)))⟩
  obtain ⟨q,fit,bill,field⟩:=collect (occupied s) law div cost (share A x) face
  refine ⟨q,fit,bill,fun U=>?_⟩
  have blank : (s,J.quiet)∈splits s:=by
    apply mem_filter.mpr
    exact ⟨mem_univ _,by simp [Poly.merges,Census.quiet]⟩
  have comp (z : J.Mode×J.Mode) (hz : z∈splits s) : z.2=J.quiet ↔ z=(s,J.quiet) :=by
    constructor
    · intro empty
      exact Prod.ext (Subtype.ext (by simpa [empty,Census.quiet] using (valid hz).2)) empty
    · rintro rfl; rfl
  have erase : occupied s=(splits s).erase (s,J.quiet):=by
    ext z; simp only [occupied,mem_filter,mem_erase]
    exact ⟨fun h=>⟨fun e=>h.2 ((comp z h.1).2 e),h.1⟩,
      fun h=>⟨h.2,fun eq=>h.1 ((comp z h.2).1 eq)⟩⟩
  have quiet:=Hard.packet_of_quiet A.K x U (old U)
  change (A.gas x U).part J.quiet=(P.activities.gas P.p U:ℂ) at quiet
  have one : share A x (s,J.quiet) U=(P.eval U:ℂ)*soft A x s U :=by
    rw [share,quiet]; simp only [Rep.eval,Complex.ofReal_mul];ring
  rw [field,erase]
  change (∑ z∈(splits s).erase (s,J.quiet),share A x z U)=(A.density x U).part s-(P.eval U:ℂ)*soft A x s U
  rw [WilsonCenteredMaskPieces.density,←one]
  exact (eq_sub_iff_add_eq).2 (sum_erase_add (splits s) (fun z=>share A x z U) blank)

end Components

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Space" => Config G (R.family.side b per)



local notation "v₀" => R.alloy.B.a.clock.forcedAllowance b

include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p:ℕ){tol:ℝ}(positive:0<tol)
    (late:WilsonSingleHardRadius.start R simple p positive ≤ b)
    {V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    (o:V→Site (R.family.side b per))(G₀:Gallery X ι o (Ψ b) J)(x:X)(s:J.Mode)
    (Z:Support (R.family.side b per))(y:Site (R.family.side b per))(center:y∈Z)
    (resident:∀a∈s.val,o a∈Z)(w:V→ℝ)(radii:∀a,0<w a){E hard:ℝ}
    (regular:G₀.E.Paid w (Ψ b).p.B ((Ψ b).p.supportExponent+2) E)
    (forced:G₀.K.Paid w (Ψ b).p.B (Ψ b).p.supportExponent hard){i:ℕ}(ui:u ≤ i)(ib:i ≤ b):
    let fare:=WilsonFullFaceSignedHard.fee (Ψ b).p Z w s E hard v₀ κ
    ‖actualTransport R.family (N:=N) (fun U=>((Ψ b).eval U)⁻¹ •
      ((G₀.density x U).part s-((Ψ b).eval U:ℂ)*soft G₀ x s U)) ib 1‖≤
      4*(1+max 0 fare)*tol/β^p:=by
  intro fare
  have walk:=course.1.walk b (floor.trans ub) cut.le
  obtain ⟨keeper⟩:=WilsonCenteredCourseKeeper.original R course b (floor.trans ub) cut
  obtain ⟨div,hv,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec b capture
  rw [←walk.truep.point] at room
  obtain ⟨q,format,bill,field⟩:=owned (F:=F) G₀ x s A Z y center resident keeper w radii walk.truep.valid hv room div regular forced
  have first:0<1+max 0 fare:=by linarith only [le_max_left (0:ℝ) fare]
  have cap:fare≤1+max 0 fare:=by linarith only [le_max_right (0:ℝ) fare]
  simpa only [field] using WilsonMeasuredOwnerFlatCourse.order R π Γ Ψ course cut.le S A y q format bill
    simple way D Q ticket floor ub fixed first cap ui ib p positive late

end YM.Integration.WilsonOriginalFlatOccupiedFace
end

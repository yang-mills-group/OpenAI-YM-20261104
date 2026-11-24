import YM.Integration.WilsonOriginalNullCanonical
import YM.Integration.WilsonThermometerSameWalkSplit
import YM.Integration.WilsonOriginalNullTransition
import YM.RG05Readout.Address.Rail
import YM.Extra.SOURCE_HISTORIES.Beside

/-! The exact positive-primary part of the original one-step signed transfer.
It uses the upper and lower vacuum already enrolled on this Concourse. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkPositive

open Function Filter Set Lattice RG Pressure Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat Legato Graces
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Next.Foundations Labels Peak Mercury
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} (R : Run G) {m N per k i d : ℕ}
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (start : m ≤ i) (live : i < N)
local notation "U" => Ψ (i+1)
local notation "B" => R.alloy.B.a.budget i
local notation "Ω" => R.alloy.B.a.clock.op i per
local notation "L" => R.rolls.L (R.alloy.B.a.clock.J (i+1))
local notation "p" => R.metals.p.profile (R.alloy.B.a.clock.J i)
local notation "room" => QuadraticLocal.Advent.spare R π Γ Ψ course (Nat.le_succ_of_le start) live
local notation "zeroI" => WilsonOriginalNullHouse.point

open Marker RemainderComparison.Serif WilsonOriginalNullAdmission WilsonOriginalNullComplex
open QuadraticLocal RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse Source
open RemainderComparison.Typeface RemainderComparison.Serif RemainderComparison.Sleet
open AllOrder.Floe.Step PlanV WheelP Mallow Fusion.Attached
local notation "F₀" => (Labels.frames G).level d
local notation "T₀" => localSection G d
local notation "divisor" => LocalComparison.forcedDivisor R.family i
local notation "high" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "upperW" => Next.Foundations.price G (max (U).p.order (U).p.power)
local notation "lowerW" => Next.Foundations.price G (max (B).order (B).power)
local notation "ρ" => Local.factor (hol G) (T₀) (B).supportExponent lowerW
local notation "scale" => ((L).val:ℂ)^d


open Trace.Physical.GermGraph Trace.Physical.Germ
open Extra.Histories.Relay
open RG05Readout.Address
local notation "Cf" => R.family

include course start live in
theorem vacuum (b:ℂ) :
    (Ω).push (U).beta (fun W=>b*((U).eval W:ℂ)) =
      fun W=>b*((Ψ i).eval W:ℂ):=by
  let upper:=QuadraticLocal.Advent.later R π Γ Ψ course (start.trans i.le_succ) live
  let lower:=QuadraticLocal.Advent.later R π Γ Ψ course start live.le
  have ub:(U).beta=(Cf).path.β N per (i+1):=upper.beta
  have uv:(U).eval=((Cf).path.rep N per (i+1)).eval:=upper.view
  have lv:(Ψ i).eval=((Cf).path.rep N per i).eval:=lower.view
  have pay:(Ω).push (U).beta (U).eval=(Ψ i).eval:=
    (congrArg₂ (fun (c:ℝ) (f:Config G ((Cf).side (i+1) per)→ℝ)=>(Ω).push c f) ub uv).trans
      ((R.makes.wilson.steps N per i live).1.symm.trans lv.symm)
  funext W
  have mul:=congrFun (RG05Readout.Address.preserves (G:=G) (Ω) (U).beta (fun V=>((U).eval V:ℂ)) b) W
  have hw: (Ω).push (U).beta (fun V=>((U).eval V:ℂ)) W =
      (((Ω).push (U).beta (U).eval W:ℝ):ℂ):=by
    simp only [StepData.push,Complex.real_smul,←Complex.ofReal_mul,integral_complex_ofReal,smul_eq_mul]
  change (Ω).push (U).beta (b • (fun V=>((U).eval V:ℂ))) W=_
  exact mul.trans (congrArg (b*·) (hw.trans (congrArg Complex.ofReal (congrFun pay W))))

include course start live in
theorem original (simple : G.Simple) (way : WayStation R.kit)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (tab : D.Tab R.rolls) (ticket : TicketP R.alloy R.kit D tab) (C₀ : Marker.Census Unit)
    (ready : WilsonOriginalNullContraction.Ready R i d)
    (fine : WilsonOriginalNullContraction.Ready R (i+1) d)
    (o : Site ((Cf).side (i+1) per)) (v : (F₀).Coeff):
    let a0:=(Ω).ratio.parent o
    let bill:=((L).val:ℝ)^d*(4*ρ+1)*(U).p.mass ((T₀).footprint o) (upperW*(F₀).coeffSize ((F₀).core v))
    ∃ Y:Coefficient (F₀) ((Cf).side i per), Y.Format a0 (hol G) (Ψ i) ∧
      Y.remBound a0 (Ψ i) divisor bill ∧
      Y.density a0 (T₀) (Ψ i) =
        transition (C:=(Cf)) d N per i ((primary o v).density o (T₀) (U)):=by
  intro a0 bill
  have clear:(F₀).core v 0=0:=by simp [Frame.core]
  obtain ⟨Z,fit,paid,_,reading⟩:=WilsonOriginalNullCanonical.original R π Γ Ψ course start live simple way
    D tab ticket C₀ ready fine o ((F₀).core v) clear
  let u:=(primary a0 ((scale*(v 0)) • (F₀).e0))
  have kh:0<divisor:=Real.sqrt_pos.2 (Real.exp_pos _)
  have up:u.remBound a0 (Ψ i) divisor 0:=primary_rem _ kh
  have uf:u.Format a0 (hol G) (Ψ i):=primary_format _
  obtain ⟨join,rate⟩:=presentation fit paid uf up
  refine ⟨beside Z u,join,by simpa only [add_zero] using rate,?_⟩
  let H:=QuadraticLocal.Advent.later R π Γ Ψ course (start.trans i.le_succ) live
  let low:=QuadraticLocal.Advent.later R π Γ Ψ course start live.le
  let f:=(primary o ((F₀).core v)).density o (T₀) (U)
  let g:=fun W=>(v 0)*((U).eval W:ℂ)
  have income:((primary o v).density o (T₀) (U))=f+g:=by
    funext W
    exact WilsonThermometerSameWalkSplit.unit (T₀) (U) o v W
  have hf:Integrable f (prior G _):=((primary o ((F₀).core v)).envelope (T₀) H.truep.valid
    (primary_rem (o:=o) _ zero_lt_one) (primary_format (H:=hol G) _)).integrableC _
  let g₀ := (primary o (F₀).e0).density o (T₀) (U)
  have h0:Integrable g₀ (prior G _):=((primary o (F₀).e0).envelope (T₀) H.truep.valid
    (primary_rem (o:=o) _ zero_lt_one) (primary_format (H:=hol G) _)).integrableC _
  have g_eq:g=(v 0) • g₀:=by
    funext W
    change (v 0)*((U).eval W:ℂ)=(v 0)*((primary o (F₀).e0).density o (T₀) (U) W)
    rw [unit_density]
  have hg:Integrable g (prior G _):=g_eq ▸ h0.smul (v 0)
  have Lb:(Cf).S.block i=L:=PriceCompiler.block_eq R.alloy.B.valid i
  have temperature:(U).beta=(Cf).path.β N per (i+1):=H.beta
  have received:Z.density a0 (T₀) (Ψ i)=transition (C:=(Cf)) d N per i f:=by
    funext W
    change _ = (((Cf).S.block i).val:ℂ)^d * (Ω).push ((Cf).path.β N per (i+1)) f W
    rw [Lb,←temperature]
    exact reading W
  have unitread:u.density a0 (T₀) (Ψ i)=transition (C:=(Cf)) d N per i g:=by
    have vac:=vacuum R π Γ Ψ course start live (v 0)
    funext W
    rw [show u=primary a0 ((scale*(v 0)) • (F₀).e0) from rfl,primary_density,map_smul,smul_eq_mul]
    have one:=congrFun (unit_density (T₀) (Ψ i) a0) W
    rw [primary_density] at one
    change _ = (((Cf).S.block i).val:ℂ)^d * (Ω).push ((Cf).path.β N per (i+1)) g W
    rw [Lb,←temperature,show (Ω).push (U).beta g W=_ from congrFun vac W]
    change ((Ψ i).eval W:ℂ)*((scale*(v 0))*_)=scale*((v 0)*_)
    exact (mul_left_comm _ _ _).trans ((congrArg (fun z:ℂ=>(scale*(v 0))*z) one).trans (mul_assoc _ _ _))
  rw [income,transition_add d N per hf hg,←received,←unitread]
  exact plus low.truep.valid paid up (T₀)

end YM.Integration.WilsonThermometerSameWalkPositive
end

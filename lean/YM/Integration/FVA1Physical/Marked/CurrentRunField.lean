import YM.Integration.FVA1Physical.Marked.QuayLampSpatial
import YM.Integration.FVA1Physical.Marked.RunFiber

/-! Current-birth physical stencils, arbitrary common physical root and
independent placements, on the very Run used by the independent FVA2 bank.
The missing-mask product and the unit term are included before blocking. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson Source Labels Precision RG.Supply Input Org Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch Roof Push.PriceCompiler UVNext.CouplingReset Next.Foundations Graces Roost
open LocalLTE LocalLTE.Vinca LocalLTE.Concourse MergeProof Planned.GuardedAtom Planned.GuardedAtom.Guard
open Push Push.Local Push.AbsoluteSums RGComparison.Core16.Spool GapsR2RG GapsR2RG.Anchor
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] {d:ℕ} (R:Run G) {N n m:ℕ} 
local notation "H" => R.family.path
local notation "RI" => (H).rep N n (m+1)
local notation "RO" => (H).rep N n m
local notation "K" => (H).levels.clock.op m n
local notation "F0" => (frames G).level 0
local notation "D0" => localSection G 0
local notation "δ" => (H).levels.clock.forcedAllowance (m+1)

theorem current_run_field (simple:G.Simple) (hm:m < N) (start:R.t 0 ≤ m)
    (a:I → CoverLabel G d) (ready:∀ j,R.t (a j).1.val ≤ m+1)
    (y:Site (R.family.side (m+1) n)) (o:I → Site (R.family.side (m+1) n)) (part:Bool)
    (radius:ℕ) (foot:∀ j,separation (o j-y) 0 ≤ radius) :
    let v:=fun j=>o j-y
    let φ:=fun U=>look part (tally (freshLamps a) o U)
    let φ₀:=fun U=>look part (tally (freshLamps a) v U)
    let z:=(K).ratio.parent y
    let cost:=Doors.rate ((H).S.block m)*birthCost (RI).p (lampSupport a v) δ
      (localFieldTariff (RI).p a (R.alloy.B.a.params (m+1)).columns radius+‖(φ₀ 1:ℂ)‖)
      (2*stencilBound (freshLamps a))
    ∃ Q:Coefficient F0 (R.family.side m n), Q.Format z (hol G) RO ∧
      Q.density z D0 RO=(K).push (RI).beta (fun U=>((RI).eval U:ℂ)*(φ U:ℂ)) ∧
      Q.remBound z RO (kappa H m) cost := by
  intro v φ φ₀ z cost
  let T:=lampSupport a v
  let f:=fun U=>(φ₀ U:ℂ)
  let u:=localFieldTariff (RI).p a (R.alloy.B.a.params (m+1)).columns radius
  let e:=2*stencilBound (freshLamps a)
  obtain ⟨shape,jets,osc⟩:=fresh_lamp_inputs R.T R.makes a hm ready v part radius foot
  let Z:=Keeper.sufficient (R.tuning.receipts.samples simple N (m+1) n hm)
  let berths:=Z.supply (fun _:ℕ=>T)
  let Y:=Vault.draw F0 RI T f berths
  have hp:=R.makes.wilson.represents N n (m+1) hm
  have hd : 3 ≤ R.alloy.B.a.clock.J (m+1):=(R.makes.stages 0).1.trans
    (R.alloy.B.a.fits.mono (start.trans (Nat.le_succ _)))
  have pos:=forcedPos R.alloy.B.a (m+1)
  have permit : hitWidth (RI).p*Real.sqrt δ ≤ 1 := by
    have hP : (RI).p = R.alloy.B.a.budget (m+1) := hp.vac
    rw [hP,Blush.glyph_eq]
    exact R.b.stamp _ _ (step_paid R.alloy.B.a (m+1)) 0 ((Nat.zero_le 3).trans hd) _ (R.alloy.B.valid.pays (m+1))|>.2 _ _
      (params_eq R.alloy.B.valid (m+1)) rfl
  obtain ⟨form,_,dens,_,bill⟩:=Vault.roots F0 RI T f berths (Finset.mem_insert_self ..) hp.good pos
    (Dilation.usualPerm permit pos).2 shape (hol G) D0 osc (u+‖f 1‖)
    (bound_sub shape (regular_const (f 1)) jets (bound_const (f 1)))
  have rem:Y.remBound 0 RI (kappa H (m+1)) (birthCost (RI).p T δ (u+‖f 1‖) e) := bill.bound le_rfl
  let S:(RI).activities.Moves 1 y:= Classical.choice (hp.good.labels.moves 1 y)
  have size:2 ≤ (R.family.side (m+1) n).val := by
    have hs:=(H).levels.fits.sizeT (m+1) n
    change _ ≤ (R.family.side (m+1) n).val at hs
    omega
  have moved:=rule_slide S form size
  have movedCost:=cost_slide S rem
  have truth:=convey_slide (P:=Y) (o:=0) S (R.makes.sections 0)
  rw [zero_add] at moved movedCost truth
  obtain ⟨Q,shapeQ,densQ,remQ,_⟩:=run_full_fiber simple R hm start y _ moved movedCost
  refine ⟨Q,shapeQ,densQ.trans (congrArg ((K).push (RI).beta) ?_),remQ⟩
  rw [truth]
  funext U
  change Y.density 0 D0 RI (Lattice.translate y U)=_
  rw [dens]
  have vv:=vac_pull H N n (m+1) R.makes.wilson hm 1 y U
  rw [pull_one] at vv
  change liftVac H N n (m+1) (Lattice.translate y U)*_=liftVac H N n (m+1) U*_
  rw [vv]
  have eq : tally (freshLamps a) v (Lattice.translate y U)=tally (freshLamps a) o U := by
    apply prod_congr rfl
    intro j _
    apply congrArg (freshLamps a j).action
    have hx (p:Site _) : expandAt p (Lattice.translate y U)=expandAt (p+y) U := by
      funext e; simp [expandAt,Lattice.translate,add_assoc]
    rw [hx]; simp [v]
  exact congrArg (fun w=>liftVac H N n (m+1) U*((look part w:ℝ):ℂ)) eq
end YM.Integration.FVA1Physical.Marked

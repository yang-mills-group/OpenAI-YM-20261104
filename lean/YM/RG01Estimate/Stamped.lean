import YM.RG01Estimate.Retention
import YM.RG01Estimate.Upgrade
/-!
 # Joint genuine pre-L funding for any grade list & contraction in unmarked analytic recovery.
 Does not discharge obligations of *renderings*; raw budgets now exposed as Mark CR registration
 for later producers (`Demand` optionally stipulates Envelope.R tric etc to be bought).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Chart
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Laplace Pressure ConnectedActivityE6 Coat Evoc Push Deck
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {M:Metals G} {D:Rolls M.p} (X:Demand G){A:Alloy M D}(R:Factor A)

structure Stamped : Prop where
    allowed : Routed.Allowed R
    earned m : Routed.retention R m ≤ X.retention M.p.profile R.v (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
    shipping : Shipping D R.shape A.delay R.scout X

def Demand.goal (F:Demand G) : Goal G where predicts R := Stamped F R
lemma activated (hG:G.Simple) :Funds X.goal:=by
    intro s T R E hc C z bt he
    have hp i j:(R j i).rate + (3/8:ℝ) < 0:= by have h:=(E j i).reach; rw [he] at h; linarith only [h]
    obtain ⟨u,hU⟩:= Activation.preprice R hp
    obtain ⟨Y,hy⟩:= rprice X s.profile z
    refine ⟨u⊔Y,fun l hl D w U Z φ S θ p Q V hJ=>?_⟩
    let M:= UVExtension.Case.provider s T l
    obtain ⟨he',hy'⟩:= sup_le_iff.mp hl
    have hR : Activation.Before (s:=ThroughLaunch.raise s l) R u:=by exact hU
    have hu j i: 0≤ Solo.raise (rays s) j i:= by have h:=(s.profile i).price_pos; exact add_nonneg (add_nonneg h.le (by norm_num)) (by norm_num)
    obtain ⟨W,hW,hA⟩:=Activation.activate p Z (rays s) mile C hG (fun j i _=> hu j i) hR (fun j=> (he' _).trans (D.large j).need) hJ V
    obtain ⟨W',hw',hB⟩:=sails (M:=M) D Z W S X (fun j i=> (he j i).trans_le (by norm_num))
    obtain ⟨V',hq,hS⟩:=margin (M:=M) D W' X z
    refine ⟨V',hW.trans (hw'.trans hq),fun W'' ht K I hp' Kx=>?_⟩
    intro A η q E X' J K' b hZ hY hm
    let F' := (⟨E,φ,S,η,q,w,K',R,_,U,Z,bt,z,rays s,mile,b,C,X',p,J,hZ,hc,hY,hm⟩:Roost.Factor A)
    refine (show Stamped X F' from ⟨hA W'' (hw'.trans (hq.trans ht)), fun m=> ?_, hB W'' (hq.trans ht)⟩)
    let x := Kx.a.clock.hatBeta m; let j:= Kx.a.clock.J (m+1); let i:= Kx.a.clock.J m
    have hi := step_paid Kx.a m
    have hK:= hS W'' ht _ _ hi x (Kx.valid.pays m)
    calc
      _ = (Height.away (s.profile i)*(z j i / ((D.L j).val:ℝ))) + Activation.glyph G (D.L j) x:=rfl
      _ ≤ _ := (add_le_add (hy j i hi (D.L j) ((hy' _).trans (D.large j).need)) hK).trans_eq (add_halves _)

-- explicit instance suitable during producer development. Can choose θ-budget via arbitrary
-- `Request`; here polynomial powers given in advance. Take δ_j=1/(j+1) for all.
-- preset stencil and powers input for example, μ
variable (G) in
def policy (φ W n:ℕ→ℕ→ℕ) : Demand G where
    retention _ _ j _ := ((j:ℝ)+1)⁻¹
    available v y j i:=inv_pos.mpr (Nat.cast_add_one_pos _)
    wish {M} D j i r := {
      meters:=φ j r
      minStudio:= n j r
      minPrice:=n j r
      loss:=((j:ℝ)+1)⁻¹
      positive:=inv_pos.mpr (Nat.cast_add_one_pos _)
      mark:=fun _ e s a b d Q=> let z:= W j r; let u (t:ℝ):= (Push.AbsoluteSums.Delay.fineMonitor G (D.L j) t)^z; e=z ∧ s=u ∧ a=u ∧ b=u ∧ d=u ∧ Q=(fun _=>True)
      incomes h l k f _ _ := by
          let z t:=(Push.AbsoluteSums.Delay.fineMonitor G (D.L j) t)^(W j r)
          have hp:Cookie G (D.L j) z:= Cookie.mast.pow _
          exact ⟨W _ _,z,z,z,z,(fun _=>True),hp,hp,hp,hp,Eventually.of_forall (fun t=> pow_nonneg (Push.AbsoluteSums.Delay.monitor_pos G _ t).le _), ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩, Eventually.of_forall fun _=>trivial⟩ }
end YM.RG01Estimate.Chart

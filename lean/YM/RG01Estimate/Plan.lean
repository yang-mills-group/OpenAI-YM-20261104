import YM.RG01Estimate.Treaties
import YM.UVExtension.Gale.Swap
/-!
 # Joint pre-L and pre-clock cost hook on the *existing UV provider*. Two applications in
 a sharing build should first conjunct their goals (no selection of new calendars after consuming).
 `Funds` is a protocol for extra costs on Factor with chosen stages/schedules, granting ANY
 legitimate preL scope (after stage's contracts and expenses), then Delay enhancements after
 protection and inspector chosen. Cannot choose L again after θ. `PlanSeals` real budget
 instance. Does not assert on ALL already chosen C. Constructor runs all orders.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Chart
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}

structure Goal (G:Gauge) where
   predicts {M:Metals G} {D:Rolls M.p} {A:Alloy M D} (R:Roost.Factor A) : Prop

def Funds (F:Goal G) : Prop := ∀ (s:Sheet G) (T:MapPrices) (R:Targets s (UVExtension.Case.actualPay s T))
       (E:Expenses R) (hc:∀ i j,(R i j).table=Next.Foundations.chart G) (C:Programs s) (z:Return.Wages) (bt:Baton G),
       (∀ i j, (E i j).wanting=-(7/16:ℝ)) → ∃ u :ℕ→ℕ, ∀ l : ℕ→ℕ,u≤l → ∀ (D:Rolls (ThroughLaunch.raise s l))
        (w:Return.Wages) (U:ℕ→ℝ) (Z:PhysicalNext.Repeat.Register D E w U) (φ:ℕ→ℕ→Postage) (S:Time.Scouts (F:=φ))
        (θ:Protection D) (p:ℕ→ℕ→JointLoad.Heir.Record) (P:PostCost D) (V:Delays θ),
         (∀ j i,Push.PriceCompiler.StepStages j i → s.first ≤ i → (p j i).ε≤1/4) →
        ∃ W:Delays θ,DelayLe V W ∧ ∀ W',DelayLe W W' → ∀ (K:Bar W')(I:Wait K)(hp:Stock.Priced W')
         (B0:Directed G I (chart G) (UVExtension.Case.actualPay s T) P),
           let A := (Alloy.mk P θ W' K I hp B0 : Alloy (UVExtension.Case.provider s T l) D)
           ∀ η q E' X J K' b,
             ∀ hZ : Roof.Sheltered (C:=C) (B:=K') A bt z (rays s) mile b X p J Z S (1/16) (1/16) (1/8) E' q η,
             ∀ hY : WorksIn (D:=D) (X:=UVExtension.Case.provider s T l) Z P W' S, ∀ hm:AsDivisors B0.a.S,
                F.predicts (⟨E',φ,S,η,q,w,K',R,E,U,Z,bt,z,rays s,mile,b,C,X,p,J,hZ,hc,hY,hm⟩: Roost.Factor A)

def Goal.both (x y : Goal G) : Goal G where predicts R := x.predicts R ∧ y.predicts R
lemma Funds.and {F Q : Goal G}(h:Funds F)(hr:Funds Q):Funds (F.both Q):=by
   intro s T R E he C z b hW
   obtain ⟨u,hu⟩:= h s T R E he C z b hW
   obtain ⟨p,hp⟩:= hr s T R E he C z b hW
   refine ⟨u⊔p, fun l h D w U Z φ S θ p P V he=>?_⟩
   obtain ⟨W,hW,hQ⟩:= hu l (le_sup_left.trans h) D w U Z φ S θ p P V he
   obtain ⟨K,hK,hQ'⟩:= hp l (le_sup_right.trans h) D w U Z φ S θ p P W he
   refine ⟨K,hW.trans hK,fun W' hu K I hp B0=>?_⟩; intro A η q E X J K' b hZ hY hm
   exact ⟨hQ W' (hK.trans hu) K I hp B0 η q E X J K' b hZ hY hm,hQ' W' hu K I hp B0 η q E X J K' b hZ hY hm⟩
end YM.RG01Estimate.Chart

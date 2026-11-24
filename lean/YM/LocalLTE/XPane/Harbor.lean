import YM.LocalLTE.XPane.Hinder
/-! Explicit Calendar for first shared canonical operation. Not uniform across choices.
-
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB
open Clock Next.Scheduling.Clock Progress.DirectedRecipe Pressure
open YM.LocalLTE LocalLTE.Fan
open Bandage.Harmonics Spiral
variable {G:Gauge} -- fix
abbrev capR (CB j _:ℕ):ℕ:= (CB+1)*(j+1)
structure Pinned {X:Metals G}{D:Rolls X.p}{C:Targets X.p X.K}{Y:Expenses C}{w:Return.Wages}{v:ℕ→ℝ}{T:Protection D}(Z:Register D Y w v)(κ:ℝ) (Q:Delays T) (M K l P p N:ℕ) (ε:ℝ):Prop where
   financed j i:StepStages j i→∀ x:ℝ,Q.betaEntry j≤x→∀ d,d ≤ i → NoDraw G d (X.p.profile j) P l p (D.L j) ε (X.p.profile i) K N x
   pawns : ∃ V:ConcertZ C M ε,V.strength=(fun _ _=> ε) ∧ V.CalendarX Z (capR K) κ (fun _ _=>K) Q
-- Actually spin engine.
variable (M K l P p T:ℕ)(ε:ℝ)(hε:0<ε)(ht:grantZ p T 0+ε≤ 0)(hq:(5:ℝ)*K+ -ε < -((P:ℝ)+1)/2)(hK: ε<M/100)
open Next.Scheduling.Clock Next.Scheduling.Instrument
include hε ht hq hK
noncomputable def thresholdX (H:Elixir G M): Elixir G M where
    invests {X _ _ _ _ _ _} R κ a b V:= H.invests (X:=X) R κ a b V ∧ Pinned (X:=X) R κ V M K l P p T ε
    pays:=by
        intro X Kf C V hc μ k h
        obtain ⟨w,hV⟩:= H.pays C V hc μ k h
        have hr j i:3/8+(C j i).rate < Mallow.aust:=by have hx:=(V j i).reach; rw [(hc j i).2] at hx; unfold aust; linarith only [hx]
        obtain ⟨Zx,he,Zq,hQ⟩:= ConcertZ.springX C (capR K) (fun _ _=> ε) (fun _ _=> ⟨le_rfl,hε,hK⟩) V hr h
        refine ⟨Zq⊔w, fun h' hW D U g B A r a Q =>?_ ⟩
        obtain ⟨hz,h₀⟩:= sup_le_iff.mp hW; obtain ⟨X',hp,hA⟩:= hV h' h₀ D A r a Q
        let Xm:= ThroughLaunch.currency X Kf h'; let Rt:Targets Xm.p Xm.K:= C
        let Zt:Mallow.ConcertZ Rt M ε:= ⟨Zx.azi,Zx.kap,Zx.bbase,Zx.amp,Zx.strength,Zx.bill⟩
        have he0:ConcertZ.ForecastX Rt (capR K) V Zt μ Zq:=hQ
        have hL(i):Zq i≤ (D.L i).val:=(hz i).trans ((D.large _).need); obtain ⟨U',hu,hT⟩:= ConcertZ.treasuryX A _ Zt μ (fun _ _=>K) he0 hL X'
        let q j i x :=∀ d:ℕ, d≤ i→ NoDraw G d (X.profile j) P l p (D.L j) ε (X.profile i) K T x
        have he'(j i:ℕ):∀ᶠ x in atTop,q j i x:=by filter_upwards [eventually_all.mpr (fun n:Fin (i+1)=> Legato.cloudY G n.val (X.profile j) P l p _ ε (X.profile i) K T (by assumption) hq)] with x hx d hd; exact hx ⟨d,Nat.lt_succ_of_le hd⟩
        obtain ⟨u,-,hy,h⟩:= collect_upper U'.betaEntry _ fun j=>eventually_transitions j _ _ (fun i _=>he' j i)
        let Q':Delays B := {U' with betaEntry:=u}
        have hK:DelayLe U' Q':= ⟨hy,le_rfl,le_rfl,le_rfl⟩
        refine ⟨Q',DelayLe.trans hp (DelayLe.trans hu hK), fun Y hv=> ⟨?_,⟨?_,Zt,he,hT _ (DelayLe.trans hK hv)⟩⟩⟩
        · exact hA _ (DelayLe.trans hu (DelayLe.trans hK hv))
        intro j i hϵ x hZ; exact h j x ((hv.beta j).trans hZ) i hϵ
end YM.PhysicalNext.Repeat.Legato

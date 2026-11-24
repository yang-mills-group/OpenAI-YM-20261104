import YM.OPE.Compatible.Mould.Harvest
import YM.OPE.Compatible.Roost.Romance
/-!
# Quotas at equal and adjacent scales

`YM.OPE.Stroke.PriceBook` supplies quotas at equal and adjacent scales and a `Sailing` satisfying `Lance` when the clip and patch side satisfy the stated bounds.
For a simple gauge group and pointwise positive `t`, `forge` constructs seasons with `T.peak ≤ t`, `κ ≤ T.gradeL`, and such a price book.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
structure PriceBook (H:LocalRatio R)(T:Seasons K):Prop where
     g i : Nonempty (Quota K T i i)
     h i : Nonempty (Quota K T (i+1) i)
     launch (P:Patch)(p:Clip)(X:Quota K T P.J P.J)(hp:p.direct≤K.γ P.J)(hq:X.minL≤P.L.val):∃ Y:Sailing T P p R (big_cost X P.L),Lance Y
variable (H:LocalRatio R)(T:Seasons K){B:P.odd_side=P.odd_side}
include H in
lemma marchZ (L:Quota K T P.J P.J)(a: Alps K T P.J v)(hx:p.direct ≤ K.γ P.J)(ht:L.minL ≤ P.L.val)(hp:a.clip=p)(hg:a.gear=Train.top P.J)(hh:∀ i:Side,Track a i)(he:1 ≤ v)(h:L.tab P.L ≤ v):∃ Y:Sailing T P p R (big_cost L P.L),Lance Y:=by
      obtain ⟨X,hP,hV⟩:=Sailing.launchAt L v he ht h ⟨P.order_cut,P.order_cut,Or.inl rfl⟩ hx H a hp le_rfl; use X; subst v; rw [heq_eq_eq] at hV; exact ⟨hV.symm ▸ hg,hV.symm ▸ hh⟩
-- Choose seasons that meet the prescribed peak and grade bounds at every stage.
lemma forge (S:Sponsor G)(H:LocalRatio R)(h:G.Simple)(t κ:ℕ→ℝ)(ht:∀ i,0<t i):∃ T: Seasons S, T.peak ≤ t ∧ κ≤ T.gradeL ∧ PriceBook H T:=by
     obtain ⟨Z,E,hZ,hE,hM⟩:= beckon G S.X S.γ (fun i=> (S.h.fit i).le); obtain ⟨T,hV,hF⟩:= seasons S h (fun i=>min (t i) (Z i)) (fun i=>max (κ i) (E i)) (fun i=> lt_min (ht i) (hZ i)); refine ⟨T,fun i=>(hV i).1.trans (min_le_left ..),fun i=>(le_max_left ..).trans (hV i).2,fun i=>(hF i).1, fun i=>(hF i).2,fun P p Q hp hB=>?_ ⟩
     let v:=max 1 (Q.tab P.L); have hz:1 ≤ v:=le_max_left ..; obtain ⟨W,hW,h₁,h₂,h₃,h₄⟩:=S.h.bottom P.J P.order_cut p hp (Train.top P.J); have hs:TicketBed S P.J p (Train.top P.J) W:=⟨hp,hW,h₁,h₂,fun i=>h₃ _ G⟩; let m(i:ℕ):Side:= ⟨i+1, Nat.zero_lt_succ _ ⟩; obtain ⟨A,-,hA,-,hb,hc⟩:= hM P.J m (tendsto_add_atTop_nat 1) p hp W (cover_revise h₁ le_rfl (paces_extend ..)).2.2.2.1 (fun n=> floor_revise (h₂ n) le_rfl (paces_extend ..)) (fun i=>h₃ (m i) G) (fun i=>h₄ rfl _)
     have hg := hb (T.peak P.J) (T.gradeL P.J) v (T.positive P.J) ((hV P.J).1.trans (min_le_right ..)) ((le_max_right ..).trans (hV P.J).2) (le_trans zero_le_one hz); let V:Alps S T P.J v:= ⟨p,Train.top P.J,W,A,hs,hA,hg⟩; refine marchZ H T Q V hp hB rfl rfl (fun i=>?_) hz (le_max_right ..)
     obtain ⟨i₀,hx⟩:= (show ∃ i',m i'=i from ⟨i.val-1,PNat.eq (by change i.val-1+1=i.val; have h:=i.pos; omega)⟩); subst i; exact (hc i₀ 3 (by decide)).2.2
end YM.OPE.Stroke

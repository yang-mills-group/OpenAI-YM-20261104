import YM.LocalLTE.Orbit.Harvest
import YM.LocalLTE.Keels.Lumens
/-! # harvest realloc calibration endpoint reserve -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open ConnectedActivityE6
open Mallow Daisy Charity Lotus
variable {G:Gauge}
open YM.LocalLTE.Dilation Push.AbsoluteSums
open LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Drift Extra.Histories
open Push Price Urns
-- supplemental.Last stencil need reserve at levels.State.S.P consuming can polynomials grow with X.R powers. Price explicit.
structure Mind (G: Gauge) (Y X:ℝ)(p d j:ℕ)(L:Side)(x:ℝ): Prop where
   limits : ∀ β :ℝ,betaF G x L /2  ≤  β→ β  ≤ 2*betaF G x L → let e:= weightC x j; let s:= powerR p β
          0 ≤ e ∧  e ≤ 1/2 ∧  e*(X*(L.val:ℝ)^d)  ≤  s  ∧  2 * X *e ≤ s ∧ 2*(1+Y)*e  ≤  s ∧  e ≤ s
variable (X Y:Stage)(p d K:ℕ)(L:Side)
lemma purchases {G:Gauge} (he:echoBit K < -(↑(p+1):ℝ)/2): ∀ᶠ x in atTop, Mind G Y.columns X.columns p d K L x:=by
    let j:=echoBit K; have hg: j  ≤  0:=bitN K; let z:= (1+Y.columns + X.columns+(X.columns*(L.val:ℝ)^d))*4
    have hf:Rate G L j (fun x=> z*weightC x K):=(Mallow.flagE L j hg).mul_left _
    have hm:j<0:= lt_of_lt_of_le he (by have h: (0:ℝ)  ≤  (p+1:ℕ):= Nat.cast_nonneg _; linarith only [h])
    filter_upwards [Urns.actualG L (↑(p+1)) _ j hf he, (Mallow.flagE (G:=G) L j hg).below hm ((1:ℝ)/2) (by norm_num),eventually_gt_atTop (0:ℝ)] with x hx hz h0
    refine ⟨fun β h hP=>?_⟩; intro a w
    have hs: 0 ≤ a:=Real.rpow_nonneg h0.le _; have hy: a ≤  1/2:= (le_abs_self _).trans hz
    have hp':z*a  ≤  w:=by have hx':=hx β h hP; push_cast at hx'; exact hx'
    have hb:1  ≤  X.columns:=X.columns_ge; have hy':1 ≤  Y.columns := Y.columns_ge
    have hq:(0:ℝ) ≤ (L.val:ℝ)^d:=by positivity
    unfold z at hp';
    have hf' : 0  ≤  X.columns*(L.val:ℝ)^d * a:= mul_nonneg (mul_nonneg (zero_le_one.trans hb) hq) hs
    have hh : 0  ≤  X.columns*a:=mul_nonneg (zero_le_one.trans hb) hs; have hK:0 ≤  Y.columns*a:=mul_nonneg (zero_le_one.trans hy') hs
    exact ⟨hs,hy,by linarith only [hp',hs,hf',hh,hK],by linarith only [hp',hs,hf',hh,hK],by linarith only [hp',hs,hf',hh,hK],by linarith only [hp',hs,hf',hh,hK]⟩
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
structure Scope (K p:ℕ){s:Sheet G}{D:Rolls s}{T:Protection D}(V:Delays T): Prop where
   estimate j i :StepStages j i → ∀ x:ℝ,V.betaEntry j  ≤  x → ∀ d ≤ i,Mind G (s.profile i).columns (s.profile j).columns p d K (D.L j) x
variable (M:ℕ)
noncomputable def reflected (G:Gauge) (he:echoBit K < -(↑(p+1):ℝ)/2) (S:Elixir G M): Elixir G M where
    invests {X _ _ _ _ _ _} R κ a0 b V:= S.invests (X:=X) R κ a0 b V ∧ Scope K p V
    pays:=by
       intro X K' C Q h k a hp; obtain ⟨w,hV⟩:= S.pays C Q h k a hp
       refine ⟨w,fun l hl D w v P Rp j J U=>?_⟩
       obtain ⟨Y,ht,hF⟩:= hV l hl D Rp j J U
       let cR i j x:= ∀ d ≤ j,Mind G (X.profile j).columns (X.profile i).columns p d K (D.L i) x
       have hh i j:∀ᶠ t:ℝ in atTop,cR i j t:=by filter_upwards [eventually_all.mpr fun d:Fin (j+1)=> purchases (G:=G) (X.profile i) (X.profile j) p d.val K (D.L i) he] with x hx; exact fun d hd=> hx ⟨d,Nat.lt_succ_of_le hd⟩
       obtain ⟨u,-,hu,hU⟩:= collect_upper Y.betaEntry _ (fun j=>eventually_transitions j _ _ fun i _=> hh j i)
       let Z: Delays P:= {Y with betaEntry:=u}; have hx:DelayLe Y Z:= ⟨hu,le_rfl,le_rfl,le_rfl⟩; exact ⟨Z,ht.trans hx,fun X h=> ⟨hF X (hx.trans h),⟨fun j i hi t hp=> hU _ t ((h.beta _).trans hp) i hi⟩⟩⟩
end YM.PhysicalNext.Repeat.Legato.Spool

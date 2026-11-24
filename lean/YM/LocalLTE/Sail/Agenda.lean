import YM.LocalLTE.Sail.Wrap
import YM.LocalLTE.Sail.Interest
/-!
# Threshold for multi-label probes in the canonical reg/history tapes
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
open Legato.Spool LocalLTE.Sail
-- post cash formulas cover all inspected accuracy. P.Stage.T.
structure Market (M K P p TT l:ℕ)(G:Gauge)(ε:ℝ) {s:Sheet G}{D:Rolls s}{T:Protection D}(V:Delays T) : Prop where
   terms j i: StepStages j i→ ∀ x:ℝ,V.betaEntry j ≤ x→
      (let y:= betaF G x (D.L j); birthFee (Doors.stain y) (marksExpense G i y) (s.profile j).supportExponent K (marksVolume G i) ≤ allocationK y ε * Urns.divisor y) ∧
      ∀ u≤ TT,Repl K ε (s.profile j) P u G (D.L j) x ∧ ∀ d ≤ i, Lagging d P u (D.L j) (s.profile j) (s.profile i) (Bandage.Harmonics.capStone s i TT) ε x G p TT l
-- register.R.K.
structure Charge (M K P p TT l q r:ℕ)(G:Gauge)(ε e κ:ℝ) {X:Metals G}{D:Rolls X.p}{C:Targets X.p X.K}{E:Expenses C}{w:Return.Wages}{v:ℕ→ℝ}{T:Protection D}(R:Register D E w v)(U:Delays T): Prop where
   inventory: Market M K P p TT l G ε U
   run: ∃ (A:Almanac)(Z:GuideF)(g:ℕ→ ConcertZ C M ε),Chronicles (X:=X) R M κ q l r p TT e U A ∧ Mobility A R U Z g K l TT κ -- arg order verify
variable {G:Gauge} (M K:ℕ){p q r l TT :ℕ}{ε e :ℝ}
variable (N:ℕ)(hx: ε≤(p:ℝ))(hz:chronicleShift TT*K + (-ε)< -((N:ℝ)+1)/2)(hN:N≤p)
open Bandage.Harmonics
include hx hz hN
lemma bank_mark {s:Sheet G}{D:Rolls s}{T:Protection D} (V:Delays T) (l:ℕ) : ∃ U:Delays T,DelayLe V U∧ ∀ Y,DelayLe U Y→Market M K N p TT l G ε Y:=by
   let f j i x:=
      (let y:= betaF G x (D.L j); birthFee (Doors.stain y) (marksExpense G i y) (s.profile j).supportExponent K (marksVolume G i) ≤ allocationK y ε * Urns.divisor y) ∧
      ∀ u≤ TT,Repl K ε (s.profile j) N u G (D.L j) x ∧ ∀ d ≤ i, Lagging d N u (D.L j) (s.profile j) (s.profile i) (Bandage.Harmonics.capStone s i TT) ε x G p TT l
   have hf j i:∀ᶠ x in atTop, f j i x:=by
      let r:= capStone s i TT; let L:=D.L j
      have h(u:ℕ)(hp:u≤ TT):∀ᶠ x in atTop, Repl K ε (s.profile j) N u G L x ∧∀ d ≤ i,Lagging d N u L (s.profile j) (s.profile i) r ε x G p TT l:=by
          have ha : chronicleShift u*K+ (-ε)< -((N:ℝ)+1)/2:= lt_of_le_of_lt (add_le_add_left (mul_le_mul_of_nonneg_right (show chronicleShift u≤ chronicleShift TT from by unfold chronicleShift; gcongr) (Nat.cast_nonneg _)) _) hz
          have hX : grantZ p TT u + ε≤ 0:=by unfold grantZ; have ht : (u:ℝ)≤ TT:=Nat.cast_le.mpr hp; linarith only [ht,hx]
          have he : grantZ p TT (u+1)< -((N:ℝ)+1)/2:=by
             have he: (N:ℝ)≤p:=by exact_mod_cast hN
             linarith only [slant p TT (u+1) (Nat.succ_le_succ hp),he]
          refine (replacement G K u L _ _ _ ha).and (?_)
          filter_upwards [eventually_all.mpr fun d:Fin (i+1)=> planting G d.val u TT p L (s.profile j) (s.profile i) N l r ε hX he] with x hp; exact fun d hd=> hp ⟨d,Nat.lt_succ_of_le hd⟩
      let P(x:ℝ):=betaF G x L; have hX:(Tendsto P atTop atTop):=Work.E09.betaF_growth G L
      filter_upwards [eventually_all.mpr (fun i:Fin (TT+1)=>h i.val (Nat.le_of_lt_succ i.isLt)),hX.eventually (employed G i K (s.profile j).supportExponent (-(4:ℝ)+ -ε)),hX.eventually (eventually_gt_atTop (0:ℝ))] with x hx he hZ
      have hp:= Real.rpow_add hZ (-4) (-ε); change _≤ P x ^ _*_ at he; rw [hp] at he
      exact ⟨he,fun i hi=>hx ⟨i,Nat.lt_succ_of_le hi⟩⟩
   obtain ⟨x,-,he,h⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ fun i _=> hf j i)
   exact ⟨{V with betaEntry:=x},⟨he,le_rfl,le_rfl,le_rfl⟩,fun _ hy=>⟨fun j i h' t hx=> h j t ((hy.beta j).trans hx) i h'⟩⟩
variable (hε:0<ε)(hK:ε≤ e)(hE: 1-e< -(↑(r+1):ℝ)/2)(ht:e < M/100)(hy:e < (3/8:ℝ)*q)(h':East.stagnate q 500<l)
    (hs:-((r:ℝ)+1)/2 ≤ grantZ p TT 0)(hu:2-e ≤ grantZ p TT 0)
include hε hK hE ht hy h' hs hu
variable (G)
noncomputable def campaign (F:Elixir G M): Elixir G M where
    invests {X _ _ _ _ _ _} R κ a b V:= F.invests (X:=X) R κ a b V ∧ Charge M K N p TT l q r G ε e κ (X:=X) R V
    pays:=by
       intro X Kf C Y hc μ k h
       obtain ⟨w,hV⟩:= F.pays C Y hc μ k h
       let Z:= Spiral.loco (G:=G) M TT (hε.trans_le hK) hE ht hy h' hs hu; obtain ⟨v,ht₀⟩:= Z.pays C Y hc μ k h
       have hr j i:3/8+(C j i).rate < Mallow.aust:=by have hx:=(Y j i).reach; rw [(hc j i).2] at hx; unfold aust; linarith only [hx]
       obtain ⟨W,hW⟩:= flexible C Y K hr (show ∀ i j,East.stagnate q (C i j).halo<l from (fun i j=> by rw [(hc i j).1]; exact h')) hε (hK.trans_lt ht) (hK.trans_lt hy) h TT -- order likely
       refine ⟨W⊔(w⊔v),fun f hf D U g B A r' a X' => ?_⟩
       obtain ⟨hδ,he₀⟩:= sup_le_iff.mp hf; obtain ⟨hx',hP⟩:=sup_le_iff.mp he₀
       obtain ⟨V₀,hX,hX0⟩:= hV f hx' D A r' a X'
       obtain ⟨V,hV,hZ⟩:= ht₀ f hP D A r' a V₀
       let Xg:= ThroughLaunch.currency X Kf f
       let C':Targets Xg.p Xg.K:= C
       have hp : Series (X:=Xg) A M μ q l r p TT e V:= hZ V (DelayLe.refl _)
       obtain ⟨u,hU⟩:= Chronicles.names hp; obtain ⟨z',g',hA,hG⟩:=hW u
       let Y'(i:ℕ):ConcertZ C' M ε:= ⟨(g' i).azi,(g' i).kap,(g' i).bbase,(g' i).amp,(g' i).strength,(g' i).bill⟩
       have he i (hi:i≤ TT) : ConcertZ.ForecastX C' (salesD z' K i) Y (Y' i) μ W:= hG i hi
       have hA':Parch u z' Y' TT l:= ⟨hA.price,hA.bound,hA.spans,hA.layers⟩
       obtain ⟨VX,hvx,h⟩:= calendars_purchase K A z' Y' W (show ∀ n≤TT, _ from he) (fun i=> (hδ i).trans (D.large i).need) V -- names
       obtain ⟨Vη,hI,hJ⟩:= bank_mark (G:=G) M K N hx (TT:=TT) hz hN VX l -- shadow hz edit.
       refine ⟨Vη,hX.trans (hV.trans (hvx.trans hI)),fun Y hy=> ⟨hX0 Y (hV.trans (hvx.trans (hI.trans hy))),hJ Y hy,⟨u,z',Y',hU.rightward (hvx.trans (hI.trans hy)), ?_⟩⟩⟩ -- structure flatten
       exact ⟨hA',h Y (hI.trans hy)⟩
end YM.PhysicalNext.Repeat.Legato.Spiral

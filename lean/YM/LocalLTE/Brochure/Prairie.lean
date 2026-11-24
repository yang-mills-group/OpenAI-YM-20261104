import YM.LocalLTE.Rendezvous.Wings
/-! # Multi-calendar for finite visitation. Doesn't change the history, chooses sufficient payments up front.
 Opportunities in chronological visiting order:
 t=0 is for m+u→m+u-1, t=1 for m+u-1→….
 t ≤ M allowed. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open YM.LocalLTE LocalLTE.Fan Pastel Marlin Animals
-- horizon M=j etc. Reservations keyed on target before.V. Strength erased.
structure Wickets (T:Targets s K)(p:ℕ)(Γ:ℝ) where
     degree : ℕ→ℕ→ℕ→ℕ
     tuner : ℕ → ConcertZ T p Γ

variable {q m:ℕ} {e:ℝ} (r: ℕ→ℕ→ℕ)
namespace Wickets
variable (T:Targets s K) (α:Expenses T)(X:Wickets T q e)
structure Corn (r:ℕ→ℕ→ℕ)(m:ℕ) (W:ℕ→ℕ): Prop where
    start : X.degree 0=r
    side (i j:ℕ)(u:ℕ): u< m →StepStages i j→2*(X.tuner u).bbase i j≤W j
    power (u:ℕ): u≤ m→ (X.tuner u).strength= fun _ _=>e
    pinch (u:ℕ):u< m→∀ (j i k:ℕ),StepStages k j→ StepStages j i→(X.tuner u).kap k j ≤ X.degree (u+1) j i +1
variable (κ:ℝ)
structure Harvest (r:ℕ→ℕ→ℕ)(m:ℕ)(W:ℕ→ℕ):Prop where
    stalk : Corn T X r m W
    star (u:ℕ): u ≤ m → ConcertZ.Forecast T (X.degree u) α (X.tuner u) κ W
variable (hR:∀ j i,3/8+(T j i).rate < Mallow.aust){κ v:ℝ}(hk:Reliable G κ v)(he:0<e)(ht:e<(q:ℝ)/100)
variable (κ)
include hR hk he ht
lemma springT (m:ℕ) : ∃ X:Wickets T q e,∃ W, Harvest T α X κ r m W:=by -- order variables r declared before.H
    have hh: ∀ (d:ℕ→ℕ→ℕ), ∃ X:ConcertZ T q e,X.strength=(fun _ _=>e) ∧ ∃ W, ConcertZ.Forecast T d α X κ W:= fun d=>ConcertZ.springL T d (fun _ _=>e) (fun _ _=>⟨le_rfl,he,ht⟩) α hR hk
    induction m with
    | zero=> obtain ⟨T',he',W,hV⟩:= hh r
             refine ⟨⟨fun _=> r,fun _=>T'⟩, W,⟨rfl,fun i j u hv=>False.elim (Nat.not_lt_zero u hv),fun i _=> he',fun i hi=>False.elim (Nat.not_lt_zero i hi)⟩,fun _ _=> hV⟩
    | succ m ih=>
       obtain ⟨X',W,hW,hP⟩:= ih
       let c:= X'.tuner; let d f (_:ℕ):= max ((c m).kap f f) ((c m).kap (f+1) f); obtain ⟨U,hU,W',hQ⟩:= hh d
       let Y:Wickets T q e:= ⟨fun i=> if i=m+1 then d else X'.degree i,fun i=> if i=m+1 then U else c i⟩
       let l j:= max (2*(c m).bbase j j) (2*(c m).bbase (j+1) j)
       let y:=(W ⊔ l) ⊔ W'
       have hi : W ≤ y:= le_sup_left.trans le_sup_left; have h₁ :W'≤y:= le_sup_right; have h': l≤ y:= le_sup_right.trans le_sup_left -- h' Pi. threshold.Trans.
       have hJ(n)(hn:n ≤ m): Y.degree n=X'.degree n ∧ Y.tuner n=c n:=⟨if_neg (by omega),if_neg (by omega)⟩
       have hE: Y.degree (m+1)=d∧ Y.tuner (m+1)=U:=⟨if_pos rfl,if_pos rfl⟩
       refine ⟨Y,y,⟨((hJ 0 (Nat.zero_le _)).1.trans hW.start),fun i j v hv h=>?_,fun t h=> ?_,fun v hv i u k he' hk=> ?_⟩,fun u hu=>?_⟩
       · rw [(hJ v (by omega)).2]; by_cases ht:v< m; exact (hW.side _ _ _ ht h).trans (hi _)
         obtain rfl : v=m:=(by omega); refine le_trans ?_ (h' j); rcases (show i=j∨i=j+1 from (by unfold StepStages at h; omega)) with rfl|rfl
         · exact le_max_left ..
         exact le_max_right ..
       · by_cases ht:t=m+1
         · rw [ht,hE.2,hU]
         rw [(hJ _ (by omega)).2]; exact hW.power _ (by omega)
       · rw [(hJ v (by omega)).2]; by_cases hu':v< m
         · rw [(hJ _ (by omega)).1]; exact hW.pinch v hu' _ _ _ he' hk
         obtain rfl:v=m:=by omega
         rw [hE.1]; apply le_trans _ (Nat.le_succ _); rcases (show k=i∨k=i+1 from (by unfold StepStages at he'; omega)) with rfl|rfl; exact le_max_left ..; exact le_max_right ..
       by_cases hl:u=m+1
       · rw [hl,hE.1,hE.2]; exact fun j i h L hv=> hQ j i h L ((h₁ j).trans hv)
       rw [(hJ u (by omega)).1,(hJ u (by omega)).2]; exact fun j i h L hv=> hP _ (by omega) j i h L ((hi j).trans hv)
end Wickets
section post
variable (R:Register D p u l)
variable (Q:Wickets X q e)(κ:ℝ)
structure Bouquets (r:ℕ→ℕ→ℕ)(m:ℕ)(V:Delays Θ):Prop where
     stalk : Wickets.Corn X Q r m (fun j=> (D.L j).val)
     fairy (u:ℕ): u ≤ m → ConcertZ.CalendarQ R (Q.degree u) (Q.tuner u) κ V
variable {W:ℕ→ℕ}(hT: Wickets.Harvest X p Q κ r m W)(hk:∀ j,W j≤ (D.L j).val)
include hk hT
lemma flowersT (V:Delays Θ): ∃ W:Delays Θ,DelayLe V W∧∀ Y:Delays Θ,DelayLe W Y→ Bouquets R Q κ r m Y:=by
    induction m generalizing V with
    | zero=> obtain ⟨W',he,h⟩:= ConcertZ.treasuryQ R (Q.degree 0) (Q.tuner 0) κ (hT.star 0 le_rfl) hk V
             exact ⟨W',he,fun Y hy=> ⟨⟨hT.stalk.start,fun i j u h=>False.elim (Nat.not_lt_zero u h), hT.stalk.power,hT.stalk.pinch⟩,fun t ht=> (show t=0 from Nat.le_zero.mp ht) ▸ h Y hy⟩⟩
    | succ m ih=>
          obtain ⟨V',he,h⟩:= ih ⟨⟨hT.stalk.start,fun i j u hu=> hT.stalk.side i j u (by omega),fun u hu=> hT.stalk.power _ (by omega),fun u hu=> hT.stalk.pinch _ (by omega)⟩,fun u hu=> hT.star _ (by omega)⟩ V
          obtain ⟨W',hy,hx⟩:= ConcertZ.treasuryQ R (Q.degree (m+1)) (Q.tuner (m+1)) κ (hT.star _ le_rfl) hk V'
          refine ⟨W',he.trans hy,fun Y hY=>⟨⟨hT.stalk.start,fun i j u hu he=>(hT.stalk.side _ _ _ hu he).trans (hk _), hT.stalk.power,hT.stalk.pinch⟩,fun t ht=>?_⟩⟩
          by_cases he:t=m+1
          · rw [he]; exact hx _ hY
          exact (h _ (hy.trans hY)).fairy _ (by omega)
end post
end YM.PhysicalNext.Repeat.Mallow

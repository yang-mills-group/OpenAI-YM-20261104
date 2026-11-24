import YM.LocalLTE.Orbit.Control
import YM.LocalLTE.ScaleX.Height
import YM.LocalLTE.Ticket.Parade
import YM.LocalLTE.Fillet.Note
/-!
# Obtaining availability, all channels. Before-L support costs integral. Use any fixed scope.H.
-/
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
variable (M q K:ℕ)(e:ℝ)
open Fan Spiral
-- rank functions *independent of* stage. customer restrictions all fine.
structure Heights where
    angle : ℕ→ℕ→ℕ -- d, j
    uplink : ℕ→ℕ -- Main need ≤angle0
    grade : ℕ→ℕ→ℕ -- bake term count from regulator charges.
structure Stature (H:Heights) : Prop where
    root d : d ≤ H.angle d 0
    pour d j : H.angle d j ≤ H.angle d (j+1)
    fitsT d : Fan.HeightPlan d q M (-e-1) (H.uplink d) (H.angle d 0)
    fitsG d j: Fan.HeightPlan (H.angle d j) q M (-e-1) (H.grade d j) (H.angle d (j+1))
lemma favors : ∃ H:Heights,Stature M q e H:=by
   choose a f hv hf using fun i:ℕ=> Fan.heightPlan i q M (-e-1) i
   let g i n:= Nat.iterate f (n+1) i -- # check notation
   have h i j : g i (j+1)= f (g i j):=by unfold g; exact Function.iterate_succ_apply' ..
   have h1 i:g i 0=f i:=rfl
   refine ⟨⟨g,a,fun i j=> a (g i j)⟩,?_⟩
   exact ⟨fun d=> hv d,fun d j=> le_trans (hv (g d j)) (h d j).symm.le,fun d=>hf d,fun d j=> (show HeightPlan (g d j) q M (-e-1) (a (g d j)) (g d (j+1)) from h d j|>.symm ▸ hf (g d j))⟩
variable (a l p:ℕ)
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
structure Terms {X:Metals G} {D:Rolls X.p} {C:Targets X.p X.K}{P:Expenses C}{h: Return.Wages}{v:ℕ→ℝ}{Y:Protection D} (R:Register D P h v)(κ:ℝ)(p a l q M K:ℕ)(e:ℝ)(A: Delays Y) (F:Heights) : Prop where
   born : Stature M q e F
   pay i j : StepStages i j → ∀ x:ℝ, A.betaEntry i ≤ x → 1≤ x ∧ l*radiusB (betaF G x (D.L i)) ≤(D.L i).val*radiusB x ∧ ∀ d ≤ j,
      let Z:= C i j; let L:=D.L i; let V:=X.p.profile i; let W:=X.p.profile j; let o:= R.o i j; let μ:= R.μ i j; let U h k n:= Fan.ManifestC Z L o (P i j) Push.SectorMeasure.Chi.canonical W.order W.power M q l h k n κ e Mallow.aust x μ
      VoucherB.Load V W l a d L e Z μ x ∧ minSide G d ≤ radiusB (betaF G x L) ∧ (∀ c:Side,(localSection G d).footprint (0:Site c)⊆Animals.neighbors (l*radiusB x) 0 ∧ (localSection G d).footprint (0:Site c)⊆Animals.neighbors (L.val*radiusB x) 0)∧ Ride W V l d a K L e Z μ x ∧ U d (F.uplink d) (F.angle d 0) ∧ (∀ n,n<K →Fan.TicketsX Z (P i j) o L μ κ W.power W.order (F.angle d (n+1)) q l x Push.SectorMeasure.Chi.canonical ∧ U (F.angle d n) (F.grade d n) (F.angle d (n+1))) ∧(∀ n≤K,Spool.BloomP G d W.supportExponent (echoBit n) x) ∧ ∀ β :ℝ,(betaF G x L)/2 ≤ β → β ≤2*(betaF G x L) → weightC x K ≤ powerR p β
   plume:32*(1+l)≤A.shells 0
   grew : ∀ i,32*(1+l)≤A.shells i
   ratio : ∀ i,1≤ A.growth i
-- Universal purchase L heights before Stature too. Dynamics frames all d on schedule. Low.Priced Width as K.Mark.
variable (H:Heights)(hQ:Stature M q e H)(hL: East.stagnate q 500 < l)(hn:1 ≤ q)
   (hW:-(((a:ℝ)+1))/2 < echoBit K)(hp: 2-e < echoBit K)(hy:echoBit K < -(↑(p+1):ℝ)/2) (ha: 1-e < -(↑(a+1):ℝ)/2)(ht:e < M/100)(hv:e < (3/8:ℝ)*q)
-- merge arbitrary existing post calendar upgrades
noncomputable def gainJ (G:Gauge) (S:Elixir G M): Elixir G M where
    invests {X _ _ _ _ _ _} R κ a0 b V:= S.invests (X:=X) R κ a0 b V ∧ Terms (X:=X) R κ p a l q M K e V H
    pays:=by
        intro X K' C P hc μ k hκ
        obtain ⟨w,hV⟩:= S.pays C P hc μ k hκ
        have hA i j : 3/8+(C i j).rate < Mallow.aust:=by have hy:=(P i j).reach; rw [(hc i j).2] at hy; unfold aust; linarith only [hy]
        have hh i j : (C i j).rate < Pastel.mini:=by unfold Pastel.mini; linarith only [hA i j,show Mallow.aust < 0 from by norm_num [aust] ]
        choose f hf using fun i j=> Fan.preciseManifest (C i j) (P i j) _ (hA i j) (show aust<0 by norm_num [aust])
        choose g hF using fun i j=> Fan.framed (C i j) (P i j) (hh i j)
        choose b hb using fun i j d:ℕ=> Spool.acquired G (X.profile j) (X.profile i) l d
        let F0(i j:ℕ):= f i j+g i j+(Finset.range (j+1)).sup (b i j)
        refine ⟨(w⊔ fromMax F0) ⊔ (fun _=>2*l), fun lA hR2 D y' x' P' R' hr a' X'=>?_⟩
        obtain ⟨h1,hp1⟩:=sup_le_iff.mp hR2; obtain ⟨h2,h3⟩:=sup_le_iff.mp h1; obtain ⟨V,h2,hPX⟩:= hV lA h2 D R' hr a' X'
        let Xg:= ThroughLaunch.currency X K' lA; let C': Targets Xg.p Xg.K:= C
        have h(i j:ℕ)(he:StepStages i j):∀ᶠ x in atTop, 1 ≤ x ∧ l*radiusB (betaF G x (D.L i)) ≤(D.L i).val*radiusB x ∧ ∀ d ≤ j,
             let Z:= C i j; let L:=D.L i; let V:=X.profile i; let W:=X.profile j; let o:= R'.o i j; let ρ:= R'.μ i j; let U h k n:= Fan.ManifestC Z L o (P i j) Push.SectorMeasure.Chi.canonical W.order W.power M q l h k n μ e Mallow.aust x ρ
             VoucherB.Load V W l a d L e Z ρ x ∧ minSide G d ≤ radiusB (betaF G x L) ∧ (∀ c:Side,(localSection G d).footprint (0:Site c)⊆Animals.neighbors (l*radiusB x) 0 ∧ (localSection G d).footprint (0:Site c)⊆Animals.neighbors (L.val*radiusB x) 0)∧ Ride W V l d a K L e Z ρ x ∧ U d (H.uplink d) (H.angle d 0) ∧ (∀ n,n<K →Fan.TicketsX Z (P i j) o L ρ μ W.power W.order (H.angle d (n+1)) q l x Push.SectorMeasure.Chi.canonical ∧ U (H.angle d n) (H.grade d n) (H.angle d (n+1))) ∧ (∀ n≤ K, Spool.BloomP G d W.supportExponent (echoBit n) x) ∧ ∀ β :ℝ,(betaF G x L)/2 ≤ β → β ≤2*(betaF G x L) → weightC x K ≤ powerR p β:=by
             let L:= D.L i; have hp0:F0 i j ≤ L.val:= (le_fromMax _ he).trans ((h3 i).trans (D.large i).need); have ha0:(f i j) ≤ L.val:=by unfold F0 at hp0;omega
             have ha1:g i j ≤ L.val:=by unfold F0 at hp0;omega
             let P1:=R'.o i j; have hb' := R'.consumes _ _ he; let Y:= X.profile j
             have he' : 2*l ≤ L.val:=(hp1 i).trans (D.large i).need; have hxL: East.stagnate q (C i j).halo < l:=by rw [(hc i j).1];exact hL
             have hε: 1≤e:=by linarith only [hp,bitN K]
             have hm(h τ υ:ℕ)(hX:Fan.HeightPlan h q M (-e-1) τ υ):= hf i j Y.order Y.power M q l h e μ k hκ (zero_lt_one.trans_le hε) ht hv hxL τ υ hX L ha0 _ P1 (R'.μ i j) hb'.1 hb'.2.1 Push.SectorMeasure.Chi.canonical
             let t n:=Fan.TicketsX (C i j) (P i j) P1 L (R'.μ i j) μ Y.power Y.order n q l
             have hw(n:ℕ):∀ᶠ x in atTop,t n x Push.SectorMeasure.Chi.canonical:= hF i j L ha1 _ _ P1 hb'.1 hb'.2.1 Y.power Y.order n q l μ k hxL hn hκ Push.SectorMeasure.Chi.canonical
             let u(d:ℕ)(x:ℝ):Prop:=
               let Z:= C i j; let L:=D.L i; let V:=X.profile i; let W:=X.profile j; let o:= R'.o i j; let ρ:= R'.μ i j; let U h k n:= Fan.ManifestC Z L o (P i j) Push.SectorMeasure.Chi.canonical W.order W.power M q l h k n μ e Mallow.aust x ρ
               VoucherB.Load V W l a d L e Z ρ x ∧ minSide G d ≤ radiusB (betaF G x L) ∧ (∀ c:Side,(localSection G d).footprint (0:Site c)⊆Animals.neighbors (l*radiusB x) 0 ∧ (localSection G d).footprint (0:Site c)⊆Animals.neighbors (L.val*radiusB x) 0)∧ Ride W V l d a K L e Z ρ x ∧ U d (H.uplink d) (H.angle d 0) ∧ (∀ n,n<K →Fan.TicketsX Z (P i j) o L ρ μ W.power W.order (H.angle d (n+1)) q l x Push.SectorMeasure.Chi.canonical ∧ U (H.angle d n) (H.grade d n) (H.angle d (n+1))) ∧ (∀ n≤ K, Spool.BloomP G d W.supportExponent (echoBit n) x) ∧ ∀ β :ℝ,(betaF G x L)/2 ≤ β → β ≤2*(betaF G x L) → weightC x K ≤ powerR p β
             have hK(d:ℕ)(hd:d≤j):∀ᶠ x in atTop,u d x:=by
                 have hy:b i j d ≤ L.val:=(Finset.le_sup (f:=b i j) (Finset.mem_range.mpr (Nat.lt_add_one_of_le hd))).trans (by unfold F0 at hp0;omega)
                 have hu(h:ℕ):∀ᶠ x in atTop,BloomP G d Y.supportExponent (echoBit h) x:= bloomP G d _ _
                 obtain ⟨v,hv⟩:= LocalLTE.Port.Sect.insideL G d
                 have hz := Urns.actualG L (↑(p+1:ℕ)) _ (echoBit K) (Mallow.flagE (G:=G) L _ (bitN K)) ‹echoBit K < _› -- only
                 filter_upwards [Work.E09.betaF_growth G L |>.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop (minSide G d)),Work.E01.radiusB_tendsto.eventually_ge_atTop v,VoucherB.pulse (X.profile i) _ _ _ _ L e _ hb'.2.1 ha, Spool.purchase (X.profile j) (X.profile i) l d a K L e (C i j) _ hW hp hb'.2.1 (hb i j d L hy) hε, hm d _ _ (hQ.fitsT d), eventually_all.mpr (fun n:Fin K=>(hw (H.angle d (n.val+1))).and (hm _ _ _ (hQ.fitsG d n.val))),eventually_all.mpr (fun n:Fin (K+1)=>hu n.val), hz] with x hδ hh hx he hw hE hv' hA
                 refine ⟨hx,hδ,?_ , he,hw,fun n hp=>hE ⟨n,hp⟩,fun n hk=> hv' ⟨n,Nat.lt_succ_of_le hk⟩,fun β h hP=> ?_⟩
                 · intro c; exact ⟨fun i hi=> (Animals.neighbors_mem ..).2 (((Animals.neighbors_mem ..).1 (hv c 0 hi)).trans (hh.trans (Nat.le_mul_of_pos_left (radiusB x) (show 0<l from Nat.zero_le _|>.trans_lt hL)))),fun i hi=> (Animals.neighbors_mem ..).2 (((Animals.neighbors_mem ..).1 (hv c 0 hi)).trans (hh.trans (Nat.le_mul_of_pos_left (radiusB x) L.property)))⟩
                 have h:= hA β h hP; push_cast at h; exact h
             filter_upwards [eventually_ge_atTop (1:ℝ), Rebuild.geometry (G.slopeConstant*Real.log ((D.L i).val)), eventually_all.mpr fun d:Fin (j+1)=> hK d.val (Nat.le_of_lt_succ d.isLt)] with x hx he hv; refine ⟨hx,?_ ,fun d hd=> hv ⟨d,Nat.lt_succ_of_le hd⟩⟩
             refine (Nat.mul_le_mul_left l (show radiusB (betaF G x L)≤ 2*radiusB x from he.1.1)).trans ?_; rw [← mul_assoc,mul_comm l]; exact Nat.mul_le_mul_right _ he'
        obtain ⟨u,-,hu,h⟩:= collect_upper V.betaEntry _ fun j=>eventually_transitions j _ _ (h j); let T: Delays P':= {V with betaEntry:=u,shells:= (fun _=>32*(1+l))⊔ V.shells,growth:=(fun _=>1)⊔V.growth}; have ht:DelayLe V T:= ⟨hu,le_rfl,le_sup_right,le_sup_right⟩
        refine ⟨T,h2.trans ht,fun Y he=> ⟨hPX Y (ht.trans he),⟨hQ,fun i j hj x hx=> (h _ _ ((he.beta i).trans hx) _ hj),?_ ,?_,?_⟩⟩⟩
        · exact (show 32*(1+l)≤ T.shells 0 from le_sup_left).trans (he.shells _)
        · intro i;exact le_trans (show 32*(1+l) ≤ T.shells i from le_sup_left) (he.shells _)
        intro i;exact le_trans (show 1 ≤ T.growth i from le_sup_left) (he.growth _)
end YM.PhysicalNext.Repeat.Legato.Spool

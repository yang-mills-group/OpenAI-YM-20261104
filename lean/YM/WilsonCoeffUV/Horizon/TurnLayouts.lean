import YM.WilsonCoeffUV.Horizon.OrbitCash
/-!
# All-period orbit of the normalized independent top-stencil polynomial

Translation in root cells (propagate with blocks) and signed relabel profile.
Estimator may re-render at each moved hull rather than rearranging an unrelated
curvature lift. T.Second preserves affine, doesn't assume gauge on correlation
mask. `s` letter price in pantry as actual spin matrices.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Motion
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι:Type}{S:Finset ι}{E W V:Credit}{m b N e h D' i a:ℕ}{G:Gauge}{A:Levels G}{R:Realm G (e+1) E}{Ñ: ChartRatio G}{T:ι→SealR G}{P:Patch}{n:Side}{σ:Signed}{D K k:ι→ℕ}
variable {H:Hol G}{F: Frame G h}{T':SectionData F}{p':h<D'}
lemma senses (L:Theatre H T' p' e E W)(t:L.V.anchor≤ m)(q:m≤ N)(v:Verse F) : Wreathe ((Shrine (L.lore N m) v).1 n) ((Shrine (L.lore N m) (paintC F σ *ᵥ v)).1 n) σ:=by
   let X:=L.lore N m; let T:= paintC F σ; let U:=imprint X T
   have hx: Shimmer X:= (production L q t).1
   have hX i: shellK (valence F i) (X.1 n i):= (hx.scan.solo i).launch _
   have hU i: shellK (valence F i) (U.1 n i):= (Solo.affixing X.1 X.2 hx.scan.solo (paintCap F σ) i).launch _
   have h i: Wreathe (affix (v i) (X.1 n i)) (affix (v i) (U.1 n i)) σ:= incense _ _ _ _ (hX _) (hU _) (hx.scan.spirit σ n i)
   rw [←Shrine_t]; unfold Shrine; simp only [Prod.fst_sum,Finset.sum_apply]; exact pulseJ _ (fun i _=>h i) (fun i _=>shell_mon (affix_shell _ _ (hX i)) (valence_cap ..)) (fun i _=> shell_mon (affix_shell _ _ (hU i)) (valence_cap ..))
lemma central_spin (L:Theatre H T' p' e E W)(u:L.V.anchor≤ m)(v:m≤ i)(g:i≤ N)(X:Verse F): let Q:= polarP L.V.draws L.V.paid T' p' N m i; Wreathe ((Q X).1 n) ((Q (paintC F σ*ᵥ X)).1 n) σ:=by
    intro Q; unfold Q polarP; rw [show steep _ _ _ _ _ _ _ _=paintC F σ*ᵥ _ from tuneSpin (N:=N) (σ:=σ) (i:=i-m) L u (by omega) X]; exact senses L (u.trans v) g _

variable [DecidableEq ι]
lemma test_cn{i:ι}(T:TowerS G (D i))(p:Cover)(v:Case D) : pPly v {i} ((cn D i T p).1 n)=Mer.skewV (wrap n p) (jot (v i) (T.1 n)):=by funext i' j x; exact petal_hit ..
lemma central_read (L:Tribe R H W V T)(u:R.anchor ≤ m)(v:m≤ i)(g:i≤ N)(X:(s:ι)→Verse (T s).F) (s:Signed)(t:ι)(p:Cover)(A:Case (fun i=>(T i).D)) : let C:=centralL R.draws R.paid N m i (T t); let Y:= X t; let Z:= cn (fun i=>(T i).D) t
    rollTest (readO A (Z (C (paintC (T t).F s*ᵥ Y)) (s.act p)) n) (readO (swish s A) (Z (C Y) p) n) s 0:=by
    intro C Y Z; unfold C; let V:=L t; let U:= V.prest.f.arch; rw [← V.prest.lands,← V.prest.modes]
    have hp:U.V.anchor ≤ m:= V.prest.tap.symm ▸ u; let Q:= paintC (T t).F s *ᵥ Y; let W:= centralL U.V.draws U.V.paid N m i (T t)
    have ht: Wreathe ((W Y).1 n) ((W Q).1 n) s:= central_spin U hp v g Y; have hv X: shellK (T t).h ((W X).1 n):= (tournure U X (hp.trans v) g).launch n
    unfold readO; intro Z' A' B' X X' H; unfold Z; rw [test_cn,test_cn, ← wrap_signed]; apply rotation_needed _ _ _ (jot_length (A t) (hv Q)) (jot_length _ (hv Y)) _ (wrap n p) H; intro F H x Y Y' E; exact ht _ E
def portraitT (T:ι→SealR G)(s:Signed)(X:(i:ι)→ Verse (T i).F):=fun i=> paintC (T i).F s *ᵥ X i
lemma revolves (L:Tribe R H W V T)(u:R.anchor≤ m)(x:m≤ N)(P:(s:ι)→Verse (T s).F)(s:Signed) : let U:= coatA R.draws R.paid N m T; litSpin s (U P) (U (portraitT T s P)):=by
    intro U t S n V; by_cases p:S.card=1
    · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp p; unfold U; rw [coatLeaf,coatLeaf]; exact central_read L u x le_rfl P s i _ V
    unfold U; rw [coatLazy _ _ _ _ _ _ _ _ p,coatLazy _ _ _ _ _ _ _ _ p,read_emp,read_emp]; intro z; rw [map_zero,map_zero]
lemma column_spin (L:Tribe R H W V T)(u:R.anchor ≤ m)(v:m≤ N)(t:b≤ N)(s:Signed)(X:(i:ι)→ Verse (T i).F):
    let k i:=(T i).h; let V:=fun x=> Gears R.draws R.paid k k N N b (coatA R.draws R.paid N m T x)
    litSpin s (V X) (V (portraitT T s X)):=by
    intro k V; exact allSpins (cloister L X u v) (cloister L (portraitT T s X) u v) (revolves L u v X s) t le_rfl R.hG R.green
end YM.WilsonCoeffUV.Wheel.Motion

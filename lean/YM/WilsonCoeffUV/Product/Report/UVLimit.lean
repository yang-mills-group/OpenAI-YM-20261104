import YM.WilsonCoeffUV.Product.Report.ReportStability
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# UV limits of reports
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b b' v u m M N a:ℕ}{H:Hol G} {x δ Z y:ℝ} {E W V' W':Credit}{R:Realm G (e+1) E}
variable {c':ℕ}{Q:Fin (a+1)→SealR G}
variable {F:Frame G h}{T:SectionData F}{p:h<D}{w:Rails h k u e}{K V' W':Credit}
abbrev lodgeIn (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(Φ:Wilt Q)(X:ℕ→Herit Q)(m b j k:ℕ): Verse F:= fun x=>PowerSeries.mk fun e=> coming fun n=> coeff e (Reports A Ñ T p Φ (X n) m b j n k x)
def Shipment (K: Schedule)(m:ℕ)(Q:Fin (a+1)→SealR G)(A: Fin (a+1)→ℝ)(e:ℕ)(X:ℕ→ Herit Q): Prop:=∀ N M b:ℕ, m≤ b → b≤ N→b≤ M→ Sitting Q A e (trailC K m b) (X N) (X M)
-- Endpoint comparison to limits (actual stencil interpretation remains to compare in RG04)
theorem reportUV (H:Hol G)(Q:Fin (a+1)→ SealR G)(T:SectionData F)
    (p:h<D)(w:Rails h k u e)(g:capP Q≤k)(E W U V B L:Credit)
    : ∃ C:Credit,
    ∀ (Y:Torch H T p w E W U)(P:ChorusLine H T p e E W V), P.arch=Y.L → let R:=Y.L.V;
    HorizonP H R W V Q → SpringD R (capP Q) u (capP Q+2) B →
    Dormitory R (capP Q) u L →
    ∀ m b j (Φ:Wilt Q)(X:ℕ→Herit Q)(A B:Fin (a+1)→ℝ)(Z:ℝ),
    R.anchor ≤ j → j ≤ b → b ≤ m → Compar R.draws.S R.y j m ≤ Z →
    Bough Q Φ (paceT R.draws.S m b) Z B → Shipment R.draws.S m Q A e X →
   ∀ i≤ e,∀ l:Alma F, let t:= ∏ i,B i*A i; let f n:= coeff i (Reports R.draws R.paid T p Φ (X n) m b j n k l); let V':= coeff i (lodgeIn R.draws R.paid T p Φ X m b j k l); Tendsto f atTop (𝓝 V') ∧∀ c N:ℕ,m ≤ c → c ≤ N → twain (C.buy Z*t) (R.tempC m c) (f N) V':=by
    obtain ⟨C,hC⟩:= tallPair H Q T p w g E W U V B L
    refine ⟨C,?_⟩; intro Y P H' R q v t m b j F X A' B' Z he hN hM hg hf hv i h l T' f x
    have ht n (hn:m≤ n) c u (p':n≤ c)(q':n≤u): twain (C.buy Z*T') (R.tempC m n) (f c) (f u) := hC Y P H' q v t m b j c u n F (X c) (X u) A' B' Z he hN hM hn p' q' hg hf (hv _ _ _ hn p' q') i h l
    have he: Tendsto f atTop (𝓝 x):= by rw [show x=coming f from coeff_mk ..]; apply augC (δ:=fun n=>C.buy Z*T'* R.tempC m n) (by simpa using (PathCost.fade R.draws.S m).const_mul (C.buy Z*T')) ((eventually_ge_atTop m).mono fun b y n u p q=> (ht b y n u p q).gap)
    exact ⟨he,fun c N y p=> lastTw he ht c y p⟩
-- identical masters. no residual topology on changing master domains
lemma shipments_one (X:Herit Q)(e:ℕ): ∃ A: Fin (a+1)→ℝ,∀ S:Schedule,∀ m, Shipment S m Q A e (fun _=>X):=by
   let P i:= ∑ j:Alma (Q i).F,∑ r:Fin (e+1), ‖coeff r.val ((X i) j)‖; have hp i:0≤ P i:= Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> norm_nonneg _
   refine ⟨P,fun S m _ _ _ _ _ _=>⟨hp,fun i j k l=>?_⟩⟩; let v:Fin (e+1):=⟨j,by omega⟩; exact twain.one _ _ (trail_pos ..).le ((Finset.single_le_sum (f:=fun r:Fin (e+1)=> ‖coeff r.val ((X i) l)‖) (fun _ _=> norm_nonneg _) (Finset.mem_univ v)).trans (Finset.single_le_sum (f:=fun h=> ∑ r:Fin (e+1), ‖coeff r.val ((X i) h)‖) (fun _ _=> Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ l)))
-- optional wick-W lift finite ordered factors, needs West structural receipts. Accept any chosen physical inputs in off-shell letter basis after same leading quote, no claim on metric Gram. Herm translation in RG10.
def PermuteLens (A:Levels G)(Ñ:ChartRatio G)(P: SealR G)(N m:ℕ)(X:P.Rider) : P.Rider := let W:= Wray A Ñ P.ans P.path N m; fun i=> ∑ j,(W⁻¹ i j) • X j
structure AheadT (H:Hol G)(R:Realm G (e+1) E)(W V:Credit)(Q: SealR G)(A:Credit) where
   p: PassportC H R Q W V
   stamps: Weston p.f.arch A
abbrev FramesR (H: Hol G)(R:Realm G (e+1) E)(W V:Credit)(Q:Fin (a+1)→ SealR G)(A:Credit): Prop:= ∀ i,Nonempty (AheadT H R W V (Q i) A)
lemma colormoon (H:Hol G)(P:SealR G)(e:ℕ)(E W V W':Credit): ∃ C:Credit,∀ (R:Realm G (e+1) E)(_S:AheadT H R W V P W'),
    ∀ X Y:P.Rider,∀ m b N M,R.anchor≤m→ m≤ b → b≤N → b≤ M →∀ A:ℝ,0≤A→Terms e P A (R.tempC m b) X Y
    → Terms e P (R.cash C m*A) (R.tempC m b) (PermuteLens R.draws R.paid P N m X) (PermuteLens R.draws R.paid P M m Y):=by
    obtain ⟨B,hB⟩:= belt (C:=W') (T:=P.ans) (p:=P.path) (e:=e) (H:=H) (E:=E) (W:=W)
    let V:= (Fintype.card (Alma P.F):ℝ)*2; let C:=(pur V).prodC B; refine ⟨C,?_⟩; intro R S X Y m b N M p v q t A hv h i g j
    let Z:= R.cash B m; let u:=R.tempC m b; have ht:0≤u:= (trail_pos ..).le
    let K k:=(Wray R.draws R.paid P.ans P.path k m)⁻¹; have hp:= R.depth _ p; have hz:0≤Z:=zero_le_one.trans (B.purchase hp)
    have hh k:twain Z u (K N j k) (K M j k):=by
       have ht:=hB S.p.f.arch S.stamps m b N M (S.p.tap.symm ▸ p) v q t j k; dsimp only [tempC,cash] at ht; rw [S.p.depths, S.p.lands, S.p.modes] at ht; exact ht
    simp only [PermuteLens,map_sum,map_smul]; apply (twain.sum Finset.univ (fun k _=>(h i g k).μ (hh k))).lift _ ht
    change (∑ _ : Alma P.F, 2*A*Z) ≤ _
    unfold C cash; rw [Credit.products]; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal V (R.y m)) hz) hv); unfold V; simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; exact le_of_eq (by unfold Z cash; ring)
-- P post Procurement receipts for standalone
lemma steering (H:Hol G)(Q: Fin (a+1)→SealR G)(e:ℕ)(E W V W':Credit):∃ C:Credit,∀ (R:Realm G (e+1) E),
    FramesR H R W V Q W' →∀ m:ℕ,R.anchor≤ m→∀ A:Fin (a+1)→ℝ,∀ X: ℕ→ Herit Q, Shipment R.draws.S m Q A e X
    → Shipment R.draws.S m Q (fun i=> R.cash C m*A i) e (fun N i=>PermuteLens R.draws R.paid (Q i) N m (X N i)):=by
   choose C h using fun i=> colormoon H (Q i) e E W V W'
   obtain ⟨V',hV⟩:= moth Finset.univ C; refine ⟨V',?_⟩; intro R f m p A X v n l b hm hn hM; let Q':= v n l b hm hn hM; have hy:= R.depth _ p
   refine ⟨fun i=>mul_nonneg (zero_le_one.trans (V'.purchase hy)) (Q'.stock i),fun i=>?_⟩
   obtain ⟨q⟩:= f i; exact fun j v k=>(h i R q (X n i) (X l i) _ _ n l p hm hn hM _ (Q'.stock i) (Q'.track i) j v k).lift (mul_le_mul_of_nonneg_right (hV i (Finset.mem_univ _) _ hy) (Q'.stock i)) (trail_pos ..).le
lemma clear_pos (φ:Rarity D)(ψ:Rarity h)(p:Disjoint (tsupport φ.ψ.val) (tsupport ψ.ψ.val)):∃ x:ℝ,0<x ∧ ClearDay φ ψ x:=by
   let P:= tsupport φ.ψ.val; let T:= tsupport ψ.ψ.val; let X:= P×ˢT
   have hp (D:ℕ)(φ:Rarity D): IsCompact (tsupport φ.ψ.val):=(ProperSpace.isCompact_closedBall 0 φ.radius).of_isClosed_subset isClosed_closure φ.support
   have hX:IsCompact X:= (hp D φ).prod (hp h ψ); by_cases Hv:X.Nonempty; swap; · exact ⟨1,one_pos,fun a ha b hb=> (Hv ⟨(a,b),ha,hb⟩).elim⟩
   let V (x:Point4×Point4):= dist x.1 x.2
   obtain ⟨x,h,H⟩:= hX.exists_isMinOn Hv (f:=V) (continuous_fst.dist continuous_snd |>.continuousOn); exact ⟨V x,dist_pos.mpr (fun w=>Set.disjoint_left.mp p h.1 (w.symm ▸ h.2)),fun _ ha _ hb=> H (show (_,_)∈ X from ⟨ha,hb⟩)⟩
lemma adequateZ (Q: Fin (a+1)→ SealR G)(T:Wilt Q)(u:∀ i j,i≠j→ Disjoint (tsupport (T i).ψ.val) (tsupport (T j).ψ.val))(y:ℝ): ∃ B: Fin (a+1)→ℝ,∀ᶠ Z:ℝ in atTop,Bough Q T y Z B:=by
    choose B b using fun i=> amplitudes (T i); refine ⟨B,?_⟩; have hp(i j):∀ᶠ Z:ℝ in atTop,i≠j→ ClearDay (T i) (T j) Z⁻¹:=by
      by_cases t:i=j; · exact Eventually.of_forall fun _ p=> (p t).elim
      obtain ⟨x,h,H⟩:=clear_pos _ _ (u i j t); filter_upwards [eventually_ge_atTop x⁻¹] with z g; exact fun _ a h' j v=> (show z⁻¹ ≤ x from by nth_rw 1 [←inv_inv x]; exact inv_anti₀ (inv_pos.mpr h) g).trans (H _ h' _ v)
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop |y|,(eventually_all).mpr (fun i=> eventually_ge_atTop (T i).radius), (eventually_all).mpr fun i=>(eventually_all).mpr fun j=>hp i j] with z h ht hy hx
    exact ⟨h,b,hy,ht,hx⟩
end YM.WilsonCoeffUV.Mer

import YM.FVA2.Extras.Four
/-!
# Producing the Response/Lucent needed for these additional fields

Suppression on `P` as in `Sweep`/`Nilp`. See `Extras/Bond` for context.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
variable {I:Type}{G:Gauge}{b d:ℤ}{r k n:ℕ}{B:Deck G}{K:Booked B}{M:MS_Data G K}
variable {P:Geo I} {F A:Glade G I}{X Y Z:T (Glade G I)}
local notation "K0"=> constantP G I (PlanetD G)
local notation "m0"=> (fun _ : I=>planeF)
lemma soft_c (H: P.θ=0)(ht:Warm F false)(he:Nilp P F): CabinF (K:=east P false) (birthTar P) F:= by
    refine ⟨fun i=>?_,ht ⟩; apply Latch.Lease.sticks ( he 1 ); intro w; simp [ Cool.stamp,Lower,Below,coldE P, H, birthTar]
lemma bloom (he:Trip (sailP m0 K0) F A)(hp:Warm F false)(hx:Bank A b): Bank F b:= by
    have hh: sailP m0 K0 F=(both G I).P F:= ( Lives.spine hp realityA ).symm; refine O.Serve.triple hp hx ⟨ he.1,?_,?_⟩
    · rw [show _+A= sailP m0 K0 F+A from congr_arg (·+A) hh.symm]; exact he.2.1
    rw [ show _+A=sailP m0 K0 F+A from congr_arg (·+A) hh.symm ]; exact he.2.2
lemma plump (he:Trip (sailP m0 K0) F A)(hp:Bank F b)(hx:Bank A b) : Velocity F ((both G I).P F + A):= by
    obtain ⟨_,hs,hU⟩:= he; have hh: sailP m0 K0 F=(both G I).P F:= (Lives.spine hp.cross realityA).symm; rw [ hh ] at hs hU; let J:=(both G I).P F + A; obtain hz : Bank J b:= hp.A.add hx
    nth_rw 1 [hU]; intro i t w; rw [funext (fun t=> swamp hs i t 0 ( v:=w ) (fun x=>Bool.noConfusion x))]; exact ( hfun (hz.cross.walk _ _ (fun x=>Bool.noConfusion x)) t ).const_add _
lemma trim_φ (hp:Warm F false)(hx:Bank A b)(he:Nilp P A)(hs:Trip (sailP m0 K0) F A): Bank F b∧ Nilp P F:= by
    obtain ht:= bloom hs hp hx; refine ⟨ ht,dustp hs.2.2 he ?_ hs.1⟩; rw [ show sailP m0 K0 F=(both G I).P F from ( Lives.spine hp realityA ).symm ]; exact ( ht.A.add hx ).cross.walk
private def ResponseTo (M:MS_Data G K)(P:Geo I)(X:T ( Glade G I )) : T ( Glade G I ) := fun k=> Nat.strongRecOn k fun k f=> wand (sailP m0 K0) (X k + Rake.lonely K0 (O.Lives.gather M P.η) (fun i=>if h:i<k then f i h else 0) k)
local notation "Λ"=> ResponseTo M P X
private lemma forward : ResponseTo M P X k = wand (sailP m0 K0) ( X k + Rake.lonely K0 (O.Lives.gather M P.η) Λ k):= by
    unfold ResponseTo; nth_rw 1 [Nat.strongRecOn, WellFounded.fix_eq]; apply congr_arg (wand _); unfold Rake.lonely; apply congr_arg ( X k + · ); refine Finset.sum_congr rfl fun i hi=>?_ ; dsimp only; rw [dif_pos (Finset.mem_Ico.mp hi |>.2)]; rfl
variable (h:P.θ=0) (hV:Banks X b)(hS:Sweep P X)
include h hV hS
private lemma secures (M:MS_Data G K)(k:ℕ): Bank (ResponseTo M P X k) b ∧ Nilp P ( ResponseTo M P X k ) ∧ Velocity (ResponseTo M P X k) ((helm M P.η (ResponseTo M P X)+ X ) k):= by
    induction k using Nat.strong_induction_on with
    | h k IH=>
      let L:= ResponseTo M P X; let W:= Rake.lonely K0 (O.Lives.gather M P.η) L k; have hA: Bank W b:= Bank.all_fin _ (fun i hi=> by simpa only [zero_add] using! ((plenary (η:=P.η) M) (k-i)).X ( IH i (( Finset.mem_Ico.mp hi ).2) |>.1 ) );
      have hD:Nilp P W:= Nilp.sum _ fun i hi=> Nilp.lonely ((IH i ( Finset.mem_Ico.mp hi |>.2 ) ).2.1);
      obtain H: Came P false (X k+W):= ⟨soft_c h (hV k|>.add hA|>.cross ) ((hS k).add hD),( hV k|>.add hA |>.heat )⟩
      obtain ⟨hK,hL⟩:= wand_C (masterD G I P) H; have hG:L k=wand (sailP m0 K0) (X k + W):= forward; have hz : Trip (sailP m0 K0) (L k) (X k+W):= hG.symm ▸ hL; obtain ⟨hp,ht⟩:= trim_φ (F:= L k) (hG.symm ▸ hK.1.mood ) ( hV k|>.add hA ) (( hS k ).add hD) hz;
      refine ⟨ hp,ht,?_⟩; rw [ Pi.add_apply, hel_core,add_assoc,add_comm _ ( X k ) ]; exact plump hz hp ( hV k |>.add hA )
lemma relieve (M:MS_Data G K): ∃ Y:T (Glade G I), Banks Y b∧Sweep P Y∧∀ n, Velocity ( Y n ) ((helm M P.η Y + X) n):= by
    exact ⟨ _,(fun i=> secures h hV hS M i|>.1),(fun i=> secures h hV hS M i|>.2.1), (fun i=> secures h hV hS M i|>.2.2)⟩
omit h hV hS
abbrev Lucent (P:Geo I)(M:MS_Data G K)(b:ℤ)(X:T (Glade G I))(Y:T (Glade G I)): Prop:= Response X M P.η b∧ Sweep P (X-Y)
lemma unique_resp (h:Lucent P M b X Y)(hp: Lucent P M b Z Y): X=Z:= by
    apply sub_eq_zero.mp; apply Cool.forget (h.1.sub hp.1) (fun _=>atBot); intro n; apply Cool.limitN (P:=P); rw [← sub_sub_sub_cancel_right X Z Y ]; exact Thin.sub ( h.2 n ) ( hp.2 n )
-- response for raw shapes
include h hV

lemma form_ψ (he: Banks Y b)(ht:Sweep P Y)(hy:∀ n,Velocity (X n) ((helm M P.η X - Y) n)): ∃ Z, Lucent P M b Z X := by
    obtain ⟨W,hW,hX,hK⟩:= relieve h he ht M; refine ⟨ X+W,⟨ fun i=>(hV i).add (hW i),fun n=>?_⟩,(by simpa using (show Sweep P W from hX)) ⟩; rw [ map_add ]; obtain hc:= Velocity.add (hy n) (hK n); rw [Pi.add_apply,Pi.sub_apply] at hc; change Velocity (X n+W n) (helm M P.η X n+helm M P.η W n); convert hc using 1 ; abel
end YM.FVA2.Extras

import YM.FVA2.Modulus
/-!
# Polynomial in the subtraction height. The order at each tuple/order is *independent*
of all positions in the separated kernel or finite profile tests. No interchange of
limits against matrix amplification.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.MS.FV2Mod
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo Vane
open Osc Fiddle Snap Book.Convolve Alps Arts City Dock Emit Mach Land Pearl Train Menus Hem Mell
open Puff Puff.Engine Puff.SplitP Puff.Actors Puff.Mom Logarithm
open scoped Topology ContDiff Interval
variable {I W J S:Type} {G:Gauge}
local notation "D"=> constantP G Unit (PlanetD G)
local notation "m0"=> (fun (_:Unit)=>planeF)
local notation "U"=> Glade G Unit
-- $H$ uniform inside anti-continuity; blade singular boundary no assumption embedded.
variable {F H:ℝ→I→Glade G Unit}
lemma latSum {E:Type} [AddCommGroup E][ Module ℝ E ] (T:Finset I){F:I→ℝ→E} (hp:∀ i∈T,Ready (F i)): Ready (fun t=> ∑ i∈T,F i t):= by simp_rw [ ← Finset.sum_apply ]; exact Ready.sums _ hp
lemma sizes (p:I→QP)(hf:Ready F)(hh:Ready H)(hf':∀ i j,Warm ( F i j ) false)(hh':∀ i j,Warm ( H i j ) false): Ready (fun v:ℝ=> fun i:I=> regionC m0 (fun _=>p i) D ( F v i ) ( H v i )):= by
   obtain ⟨n,Hf⟩:=hf; obtain ⟨d,Hh⟩:= hh; let w(r t:ℕ)(x:ℝ):=(Logarithm.plate r t).eval x; let A (i j:ℕ)(k:I):= regionC m0 (fun _=>p k ) D ( F i k ) ( H j k ); let a (x:ℝ)(i:ℕ): I→U:= ∑ j∈Finset.range d,w d j x • A i j
   obtain he₂ : ∀ i:ℝ,∀ k:I,F i k=∑ j∈ Finset.range n,w n j i • F (j:ℝ) k:= by intro i k; rw [interpret Hf i]; unfold evaluate; simp only [Finset.sum_apply]; rfl -- F i rw itself?
   obtain he₃ : ∀ i:ℝ,∀ k:I,H i k=∑ j∈ Finset.range d,w d j i • H (j:ℝ) k:= by intro i k; rw [interpret Hh i]; unfold evaluate; simp only [Finset.sum_apply]; rfl
   have ha (i:ℕ):Ready (fun x:ℝ=>a x i):= latSum _ (fun j _=> Ready.pmul (Logarithm.plate _ j) ( Ready.const ( A i j ) ) );
   convert latSum (Finset.range n) (fun i _=> Ready.pmul (Logarithm.plate n i) (ha i)) using 1; funext x k; rw [ he₂ x k, region_left _ (fun i=>w n i x) (p k) (hh' ..) (fun j _=> hf' (j:ℝ) k), he₃ x k ]; have hm (i:ℕ): regionC m0 (fun _=>p k) D ( F i k ) (∑ j∈Finset.range d,w d j x • H (j:ℝ) k)=(a x i) k:= by rw [ region_right _ (fun j=>w d j x) (p k) (hf' ..) (fun j _=> hh' (j:ℝ) k)]; unfold a; rw [Finset.sum_apply ]; rfl
   simp_rw [ hm, Finset.sum_apply ]; rfl
-- recurse over field-pins and n. uniform across all injective kernel points.
variable [LinearOrder W] {B:Local.Physical.Deck G}{O:Booked B}(M:MS_Data G O){w: W→ Rake.Label B}(x:I→ W→ Tone.QP)(h:∀ i,Injective ( x i ))
set_option quotPrecheck false
local notation "π" i=> (fun p : W=> fun _ : Unit=> x i p)
local notation "ω"=>sailP m0 D
local notation "𝚺"=> Dial.spine M w
local notation "ℝ₀" y=> approach ( Tide.frameF Unit y ) M
local notation "Α" y i=> 𝚺 y ( x i )
local notation "ι" y i => Dial.pin M w y (h i)
private def label (V:ℝ)(n d:ℕ)(F:T ( Flats G )) : Glade G Unit:= circle (fun _ :Unit=> V) (Outlook.Archive d F) n
lemma loneZ {n d:ℕ}{F:T ( Flats G )} (hp:Host (F n) d): Ready (fun y:ℝ=>fun _:I=>label y n d F):= by

    let P : ( ℝ→ Law G )→ₗ[ℝ] I→Glade G Unit := { toFun f:= fun _ _=> f, map_smul' _ _:=rfl,map_add' _ _:=rfl }; exact Ready.linear ( plant hp ) P
lemma rent_slot (w:Label B)(n:ℕ): Ready (fun y:ℝ=>fun _:I=> rowM ( Tide.frameF Unit y ) M w n ):= loneZ ( G:=G ) ( I:=I ) ( Emit.Host.host ( gang ( M.markOK w.h w.item n ) ) ) -- n implicit
lemma rent_market (n:ℕ): Ready (fun y:ℝ=> fun _:I=> approach ( Tide.frameF Unit y ) M n):= loneZ ( G:=G ) ( I:=I ) ( Emit.Host.host ( gang ( M.bulkOK n ) ) )
private lemma latSumV (T: Finset J){F:J→ℝ→ I→Glade G Unit}(h:∀ i∈T,Ready (F i)): Ready (fun k:ℝ=>fun x:I=>∑ i∈T,F i k x):= by
    convert latSum T h using 1; funext v x; rw [Finset.sum_apply ]
include h
lemma multiline (n:ℕ)(S:Finset W): Ready (fun v:ℝ=> fun i:I=> 𝚺 v ( x i ) S n):= by
   let P(v:ℝ)(i:I)(T:Finset W)(j:ℕ):= 𝚺 v (x i) T j; let k(v:ℝ)(i:I):= builder M ( YM.FVA2.Waves.moved_pin ( h i ) v ) w; -- Local notation π i
   have heq (A:Finset W)(hA:A.Nonempty)(n:ℕ)(v:ℝ)(i:I):Warm (P v i A n) false:= ( founded ( k v i ) ( Dial.pin M w v ( h i ) ) hA n ).2;
   induction S using Finset.strongInductionOn generalizing n with| _ S ih=>
       obtain H|H:= S.eq_empty_or_nonempty; · subst S; rw [show (fun v:ℝ=>fun i=>𝚺 v ( x i ) ∅ n)=0 from funext (fun v=> funext fun i=> ( Dial.pin M w v (h i) ).1 ▸ rfl ) ]; exact Ready.zero
       by_cases hs : S.card≥2; swap; · obtain ⟨s,rfl⟩:= Finset.card_eq_one.mp ( show S.card=1 from by obtain hv:= Finset.card_pos.mpr H; omega ); simp_rw [ show ∀ y:ℝ,∀ i:I,𝚺 y (x i) {s} n= rowM ( Tide.frameF Unit y ) M ( w s ) n from fun y i=> congr_fun ( (Dial.pin M w y ( h i ) ).2.1 s ) n ]; exact rent_slot (I:=I) M ( w s ) n

       induction n using Nat.strong_induction_on with| h n hi=>
        let F(v:ℝ)(i:I):= P v i S n; let Z (v:ℝ)(i:I):= Src (π i) m0 D D ( approach ( Tide.frameF Unit v ) M ) ( 𝚺 v (x i) ) S n
        have H₉(v:ℝ)(i:I): Trip ω (F v i ) ( Z v i ):= (Dial.pin M w v (h i)).2.2 S hs n
        have H₈: Ready Z:= by
           unfold Z Src multi lonely; change Ready ((fun k:ℝ=>fun i:I=> lonely D (approach ( Tide.frameF Unit k ) M) (𝚺 k (x i) S) n)+(fun k:ℝ=>fun i:I=> ∑ p∈picks S,∑ j∈ antidiagonal n, regionC m0 (rootX (π i) p-rootX (π i) S) D (P k i p j.1) (P k i ( S \ p ) j.2))); apply Ready.add; -- param error likely enough.
           · exact latSumV _ (fun i h=> tube (fun v (_:I)=> approach ( Tide.frameF Unit v) M (n-i)) (fun v x=> P v x S i) (rent_market ..) ( hi _ ( Finset.mem_Ico.mp h|>.2 ) ) )
           refine latSumV _ (fun A hp=> latSumV _ (fun j hj=>?_ )); have hm(i:I): rootX (π i) A-rootX (π i) S=(fun _ :Unit=>(rootX (π i) A-rootX (π i) S) () ):= funext fun _=> rfl; obtain hJ:= n_small hp; let xD(i:I) := (rootX (π i) A-rootX (π i) S) (); convert sizes (p:=xD) ( ih A hJ.1 j.1 ) ( ih _ hJ.2.2.2 j.2 ) ( heq A hJ.2.1 _ ) ( heq _ hJ.2.2.1 _ ) using 1
        obtain ⟨r,hR⟩:= H₈; obtain hw : ∀ t,∀ i,F t i=(evaluate r F t) i:= by
            intro t i; let u(j:ℕ):= ( Logarithm.plate r j ).eval t; let S0:=( evaluate r F t ) i; refine Duty.consistent (retire D m0) ( H₉ t i ) ?_; rw [ interpret hR t ]; unfold evaluate; simp_rw [ Finset.sum_apply, Pi.smul_apply ]; exact trip_sum _ u (fun j _=> heq S H _ _ _ ) ( fun j _=> H₉ (j:ℝ) i )
        convert eval_ready r F using 1; exact funext fun t=> funext ( hw t )
lemma booktime (n:ℕ)(S:Finset W) : Ready (fun y:ℝ=> fun i=> Dial.book M w y ( x i ) S n):= by
    let f(y:ℝ)(i:I):= 𝚺 y ( x i ) S n; let v(y:ℝ)(i:I):= Dial.book M w y ( x i ) S n;
    obtain ⟨d,hd⟩:= multiline ( w:=w ) M x h n S; change f∈ interest d _ at hd;
    convert eval_ready d v using 1; funext y i; let F(t:ℝ)(j:I):= fun s:ℝ=>f t j () s []; apply tendsto_nhds_unique ( f:=F y i ) ( YM.FVA2.Waves.gathered M w (h i) S n y () ) ?_; have ht : F y i=(fun t:ℝ=>∑ k∈ Finset.range d,(Logarithm.plate d k).eval y • F k i t):= funext fun t=> (by unfold F; rw [ interpret hd y ]; unfold evaluate; simp_rw [Finset.sum_apply,Pi.smul_apply]); rw [ht]; unfold evaluate; simp_rw [Finset.sum_apply, Pi.smul_apply ]; exact tendsto_finsetSum _ fun k _=> Tendsto.const_smul ( YM.FVA2.Waves.gathered M w ( h i ) S n k () ) _
-- lifted alphabet.Pl.
section
omit h [LinearOrder W]


private lemma onMul {F H:ℝ→I→ℂ}(hp:Ready F)(hv:Ready H): Ready (fun t:ℝ=> F t*H t):= Ready.pair (LinearMap.mul ℝ (I→ℂ)) hp hv
lemma joins (S:SplitP W)(F H:ℝ→ I→W→T ℂ) (hp:∀ i n,Ready (fun y:ℝ=>fun j=> F y j i n))(hv: ∀ i n,Ready (fun y:ℝ=>fun j=> H y j i n))(a:W)(d:ℕ): Ready (fun t:ℝ=> fun i=> S.Lift (Trunk.core) ( F t i ) ( H t i ) a d ):= by
   simp_rw [S.loan, Finset.sum_apply ]; -- nested sum; latSumV universe wrong.
   change Ready (fun t:ℝ=> fun i=> ∑ k∈ S.pieces a, ∑ j∈ antidiagonal d, F t i k.1 j.1* H t i k.2 j.2); let f k l n m (t:ℝ):I→ℂ:= (fun i=>F t i k n)*(fun i=>H t i l m);
   convert latSum (S.pieces a) (F:=fun k t=> ∑ j∈ antidiagonal d,f k.1 k.2 j.1 j.2 t ) (fun k _=> latSum _ (fun j _=> onMul (hp k.1 j.1) ( hv k.2 j.2 ))) using 1; funext s i; simp_rw [ Finset.sum_apply]; rfl
lemma timesPoly (S:SplitP W)(F:ℝ→ I→W→T ℂ) (hp:∀ w n,Ready (fun y:ℝ=> fun j=>F y j w n )) (j w n): Ready (fun t:ℝ=> fun i=> (Trunk.stack S).power ( F t i ) j w n ):= by
   induction j generalizing w n with| zero=> exact Ready.const (fun _:I=> (Trunk.stack S).unit w n)| succ j ih=> exact joins S _ _ hp ( ih ) _ _ -- ancillary w n
end
include h
lemma toured (w: W→Label B)(S:Finset W)(n:ℕ): Ready (fun y:ℝ=>fun i:I=>Dial.tour M w y ( x i ) S n):= by
   let f (t:ℝ)(i:I):= Dial.book M w t (x i); unfold Dial.tour bouquet Cheer cheers; simp_rw [Finset.sum_apply]; -- show finite spectrum.
   -- transfer sum element.W
   convert latSum _ (fun k (_:k∈Finset.range (S.card+1))=> onMul (F:=fun _:ℝ=>fun _:I=>Puff.Actors.phase k) (Ready.const _ ) ( timesPoly (marked W) f (fun i n=> FV2Mod.booktime M x h n i ) k S n ) ) using 1; -- extra W? [LinearOrder W] omitted.
   funext y i; simp_rw [ Finset.sum_apply ]; rfl
end YM.MS.FV2Mod

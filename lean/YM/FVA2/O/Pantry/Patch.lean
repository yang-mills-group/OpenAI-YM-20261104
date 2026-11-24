import YM.FVA2.O.Fusion.Reads
/-!
# `DOrd` construction even for general separated layouts

`serves`: prove via copying data from individual points, no uniform estimate
over positions here. Use `DOrd` methods from `YM/MS` (not asserting a lattice or
regulator-removal statement).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Price
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Serve Rake.Geo Vane Fuse
open scoped Topology ContDiff Interval
variable {G: Gauge}{I J:Type} { P:Geo I } {Q:Geo J} {W:Type}[LinearOrder W] {B:Deck G}{K: Booked B}{M:MS_Data G K}{n:ℕ}{ℓ:I→Filter ℝ}{k:ℤ}
variable {U:Rake.Calculator G I} {F H:Glade G I}
omit [LinearOrder W] in
lemma cull (h:Rake.Engine U)(hp: Trip U F H)(hx:Diversity H k): Diversity F k:= by
   obtain ⟨n,hn⟩:= hp.1; let K (a:ℤ):Prop:= Diversity F (max a k); have he : ∀ i:ℕ,K ( (n:ℤ)-i ):= by
      intro i; induction i with
      | zero => simp only [Nat.cast_zero,sub_zero]; exact behind hn (le_max_left ..)
      | succ i ih =>
         by_cases hl:k ≤ ↑n-i; swap; · refine behind (Y:=(max ((n:ℤ)-(i:ℤ)) k)) ih (by omega)
         let d : ℤ := ( max ( (n:ℤ)-(↑(i+1):ℤ)) k ); have ht : Diversity ( U F ) d := behind (Duty.fee ( Y:=max ((n:ℤ)-(i:ℤ)) k ) h ih) ( by unfold d; omega ); change Diversity F d; rw [hp.2.2]; exact diversity_flow ( uh ht ( behind hx ( le_max_right .. ) ) ) -- rw may rewrite U F
   let i:ℕ:= ((n:ℤ)-k).toNat; exact behind (Y:=max ((n:ℤ)-i) k) (he i) (by unfold i; omega)
variable {X Y:Rake.Dance G I W}{s: Finset W} {x:Position W I} {r:W→Rake.Label B}
abbrev snap_c (θ:J→I) : (Finset W → Rake.Site G I) → (Finset W → Rake.Site G J):= Dial.copy θ
abbrev separable (x:Position W I): Prop:= ∀ i, Injective ( Dial.pointI x i )
local notation "m0"=> fun (_:I)=> planeF
local notation "Λ"=> constantP G I (PlanetD G)
local notation "Υ"=> constantP G J (PlanetD G)
local notation "Tη"=> (fun (_:J) => planeF)
abbrev crumbs (P:Geo I)(M:MS_Data G K)(x:Position W I)(X:Rake.Dance G I W)(s:Finset W)(n:ℕ):= multi (m0) x (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach P M) (X s) X n s
set_option maxHeartbeats 300000 in
lemma crumb_copy (i:J→I)(h:Q.η=P.η∘ i):
    let V:= snap_c i X
    crumbs Q M (fun j=> x j ∘ i) V s n= ( crumbs P M x X s n ) ∘ i := by
      dsimp only; funext p t; dsimp only [crumbs,multi,lonely,expJ]; simp only [ Pi.add_apply, comp_apply, Finset.sum_apply, Dial.basis_copy ]; refine congr_arg₂ ( ·+· ) (Finset.sum_congr rfl (fun _ hp=>?_)) ( Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun j _=>?_))); · unfold approach Rake.circle nameR expJ; dsimp only; rw [ h ]; rfl
      rfl
local notation "Point" => Dial.spine
local notation "Pos" => Dial.pointI
variable (M P x r)
def patchD : Rake.Dance G I W := fun s n i=> Point M r (P.η i) (Pos x i) s n ()
variable {M P x r}
local notation "∆"=> patchD P M x r
lemma patch_copy (p:I) : snap_c (fun (_:Unit)=> p) (∆) = Point M r (P.η p) ( Pos x p ) := rfl
lemma snip (h:separable x)(i:I): DOrd K ( Tide.frameF Unit (P.η i) ) M r (fun k _=> x k i) (snap_c (fun (_:Unit)=>i) (∆) ):= by rw [ patch_copy ]; exact Dial.pin M r _ (h i)
lemma stageUp (h: ∀ p:I,DOrd K ( Tide.frameF Unit (P.η p) ) M r (fun i _=>x i p) (snap_c (fun (_:Unit)=>p) X)): DOrd K P M r x X:= by
    have he : X ∅=0 := by
       funext k i; exact congr_fun (congr_fun ( h i ).1 k) ()
    have hs (i:W): X {i}=rowM P M ( r i ):= by
       funext k p; exact congr_fun (congr_fun ( ( h p ).2.1 i ) k ) ()
    refine ⟨ he,hs,fun s k=> ?_ ⟩
    let Pred (t:Finset W)(k:ℕ): Prop:= Trip (sailP (m0) Λ) ( X t k ) (crumbs P M x X t k); change ∀ n, Pred s n
    induction s using Finset.strongInductionOn with| _ s ih =>
       have hv (p) (hp:p⊂s) (n:ℕ): collect (X p n):= by
           by_cases hx:p.card≥2; exact ( ih p hp hx n ).1
           obtain hh|hh:= p.eq_empty_or_nonempty; · rw [hh,he]; exact collect_z
           obtain ⟨j,hj⟩:= Finset.card_eq_one.mp (show p.card=1 from by obtain hx':= Finset.card_pos.mpr hh; omega); rw [hj,hs]; exact ( Response.visit (M:=M) (η:=P.η) (r j|>.item)).life n |>.heat
       intro b; induction b using Nat.strong_induction_on with| h m H =>
          let Y:=crumbs P M x X s m; let F:=X s m; let T:=sailP (m0) Λ F; have ha(i:I): Trip ( sailP (fun (_:Unit)=>planeF) (constantP G Unit (PlanetD G)) ) (fun (_:Unit)=> F i) (fun _=>Y i):= by
             change Trip _ _ (crumbs P M x X s m ∘ fun (_:Unit)=>i)
             rw [ ← crumb_copy (P:=P) (M:=M) (s:=s) (X:=X) (x:=x) (n:=m) (fun (_:Unit)=> i) (Q:=Tide.frameF Unit (P.η i)) (by rfl) ]; exact (h i).2.2 s k m -- defeq
          obtain ⟨d,hD⟩: collect Y:= collect_p ( collected _ (fun i hi=> collect_tree Λ ( (plenary (η:=P.η) M (m-i) ).heat ) ( H i (mem_Ico.mp hi|>.2) |>.1 ) )) ( collected _ (fun j hj=> collected _ fun l hl=> collect_join (m0) Λ ( hv _ (n_small hj|>.1 ) l.1 ) ( hv _ ( n_small hj|>.2.2.2 ) l.2 ) )) -- defeq
          exact ⟨⟨d,fun i=> cull ( retire .. ) (ha i) (fun _=> hD i) ()⟩,fun i=> ( ha i ).2.1 (),funext fun i=> congr_fun ( ha i ).2.2 ()⟩
lemma serves (h:separable x): DOrd K P M r x (∆):= stageUp (snip h)
end YM.FVA2.O.Price

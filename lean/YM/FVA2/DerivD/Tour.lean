import YM.FVA2.DerivD.Shift
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Smooth Lifetime Smooth.Slots MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom MS.Tide MS.Momentum
open O O.Lives
open scoped Topology ContDiff BigOperators Interval
variable {W I J: Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable [LinearOrder W][Fintype W]
variable {A:MS_Data G M}{u:W→Rake.Label b}{a:ℝ}{s t:Steps W}{q:Draw W}{E:Type}
/-!
# Derivative array readout on the full continuum MS marked kernel

`realMusic`: pointwise derivative law; from here compute with `tour`
(`symbolic`) or the `Readings` construction.
-/
open MS.Dial O.Lives Extras
local notation "Π"=> (Draw W)
local notation "χ"=> (Tide.frameF Unit a)
omit [LinearOrder W] [Fintype W] in
lemma touch (h:Injective q): Mesh (Tide.frameF Unit a) (fun i (_:Unit)=>q i):= by intro i j hi; have H:0<‖q i-q j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hi)); refine ⟨ ⟨ _,H,fun _=>?_ ⟩,⟨_,H,fun _=>?_⟩ ⟩ <;> simp [Rake.Geo.roots]
local notation "Λ0"=>frameF I a
abbrev Readings (a:ℝ)(A:MS_Data G M)(u:W→Rake.Label b): Stamp W:= fun s q=> let x:= (fun i(_:Unit)=>q i); fun T n=> Vane.blade ( Slots.curve ( Tide.frameF Unit a ) A u x s T n ) ()
abbrev Music (a:ℝ)(A:MS_Data G M)(u:W→ Rake.Label b): Stamp W:= fun s q=> bouquet ( Readings a A u s q )
omit [Fintype W] in

lemma kelps (i:I)(q:Rake.Label b)(s:List Axis)(n:ℕ)(a:ℝ)(F:MS_Data G M): beamH F (frameF I a) q s n i=beamH F (frameF Unit a) q s n () := by
    induction s with
    | nil=> rfl
    | cons v s ih=> funext t w; change Lifetime.turn _ (net w ) * _= Lifetime.turn _ _ * _; exact congr_arg ( ( Lifetime.turn _ (net w) ) * · ) ( congr_fun ( congr_fun ih t ) w )
omit [Fintype W] in

-- specialization of `Dial.valid_copy`. use same x and η. extra derivative units allowed.
lemma copied {x:Position W I}{U:Rake.Dance G I W} (hx:Slots.charted Λ0 A u s x U)(v:I): Slots.charted χ A u s (fun w _=>x w v) (copy (fun _=> v) U):= by
    unfold Slots.charted Fields; let V0:=frameF Unit a; let Y:= copy (fun (_:Unit)=>v) U;
    refine ⟨ ?_,fun i=>?_,fun i h n=>?_⟩; · funext j p; change U ∅ j v =_; rw [hx.1]; rfl
    · funext j p; change U {i} j v=_; rw [hx.2.1]; exact kelps v _ _ j a _
    let Δ:Planet G I:= constantP G I (PlanetD G); let ℓ:Planet G Unit:= constantP G _ ( PlanetD G ); let S:= Src x (fun _=>planeF) Δ Δ (approach Λ0 A) U i n; let F:= sailP (fun _=>planeF) Δ (U i n)+S; let w:I :=v;
    let T:= Src (fun i _=>x i w) (fun _=>planeF) ℓ ℓ ( approach V0 A ) Y i n;
    have hh : sailP (fun _=>planeF) ℓ ( Y i n )+T = F ∘ (fun (_:Unit)=>v):= by
       funext j t; let g:=fun (_:Unit)=> v
       change (sailP (fun _=>planeF) ℓ _+ Src (fun i=>x i ∘ g) (fun _=>planeF) ℓ ℓ (approach V0 A) Y i n) j t = _; dsimp only [ F,T,S, Src, multi, lonely, Y, copy ]; simp only [ Pi.add_apply, comp_apply, Finset.sum_apply, basis_copy ]; exact congr_arg₂ ( ·+· ) rfl (congr_arg₂ (·+·) (Finset.sum_congr rfl (fun _ _=> rfl)) ( Finset.sum_congr rfl (fun _ _=> Finset.sum_congr rfl (fun _ _=>rfl))))
    obtain ⟨⟨k,hK⟩,hS,hL⟩:= hx.2.2 i h n; change collect ( Y i n ) ∧ Latch.Job.train false ( sailP _ ℓ ( Y i n )+T ) ∧ Y i n= river (sailP _ ℓ ( Y i n )+T); rw [hh]; exact ⟨ ⟨ k,fun _ _=> hK _ _ ⟩,fun i=>hS v, congr_arg (fun U: Glade G I=> U ∘ ( fun (_:Unit)=> v )) hL ⟩
variable (hp:Injective q)
include hp
lemma at_q (a:ℝ)(A:MS_Data G M) (u:W→Rake.Label b)(s:Steps W)(T:Finset W)(n:ℕ)(p: ( setOf ( Dial.Clamp q ))): let K := frameF ( Draw W ) a; let x:= fun w=> Window w q; let X:= Slots.curve K A u x s; Readings a A u s (p:Draw W) T n= Vane.blade ( X T n ) (p:Draw W) := by
    intro K x X; obtain hK:= turnH hp a; obtain hX:= Slots.arrived (P:=K) A u s x hK; obtain h0:= copied hX p.val;
    have hh : (fun w (_:Unit)=> x w p.val) = fun w (_:Unit)=> p.val w:= by exact funext fun w=> funext fun _=> if_pos p.property
    rw [hh] at h0; let P:=frameF Unit a; unfold Readings Vane.blade; rw [perfect ( Slots.arrived _ _ _ _ ( touch ( show Injective p.val from ?_ ) ) ) h0];
    · rfl
    have hc:= Dial.detailI a hK p.val; -- ms Data u? inspect
    exact fun a b h=> hc ( show x a p.val=x b p.val from (congr_fun (congr_fun hh a) ()).trans (h.trans (congr_fun (congr_fun hh b) ()).symm) )
lemma realMusic (T:Finset W)(k:ℕ)(a:ℝ)(A:MS_Data G M)(u:W→Rake.Label b)(s:Steps W): Rides 1 T s (fun v p=> Music a A u v p T k) q:= by
    suffices he: ProperS s q (Readings a A u) by exact ( he.full T k ).1
    intro t k; constructor
    · let K:= frameF Π a; let x:=fun w=> Dial.Window w q; let F:= Slots.curve K A u x; let J:= setOf ( Dial.Clamp q ); obtain ho:= Smooth.Cruise.clamp q; have hx :∀ i,Set.EqOn ( x i ) (fun (t:Draw W)=> (1:ℝ) • t i) J:= fun _ _ hv=> ( if_pos hv ).trans ( one_smul .. ).symm;
      obtain h := Cruise.stars (x:=x) (J:=J) (V:=F) A u ho hx (turnH hp a) (fun p=> Slots.arrived A u p _ ( turnH hp a )) t k s ( mem_of_mem_nhds ( earlyW hp ) ); apply h.congr; · exact Filter.eventuallyEq_of_mem ( earlyW hp ) fun p hp'=> at_q hp a A u s t k ⟨p,hp'⟩
      intro i _; exact at_q hp a A u _ t k ⟨ q,mem_of_mem_nhds ( earlyW hp )⟩
    intro i hi; unfold Readings Vane.blade; let x := (fun t (_:Unit)=> q t); have hh:= touch (a:=a) hp; dsimp only; rw [ Cruise.parity_mark ( Slots.arrived A u (hop s i) x hh ) ( Slots.arrived A u s x hh ) t ]; intro j hj; unfold Slots.att; rw [hop_other s _ ( fun hv=> hi ( Finset.mem_product.mpr ⟨ hv,mem_univ _⟩ ) ) hj ]
omit [Fintype W] in

lemma notation_t : Music a A u s q = Extras.service a A ( Slots.att χ A u s ) (fun t (_:Unit)=> q t):= by
    let x:= (fun t (_:Unit)=> q t); funext i n; have hh:= touch (a:=a) hp; let X:= Slots.curve χ A u x s; obtain ht: Slots.charted χ A u s x X:= Slots.arrived A u s x hh; obtain hX: Extras.Survey χ A ( Slots.att χ A u s ) x:= fun i=> Extras.Estate (safe _ _).2 ( safe _ _ |>.1.1 ) _; have hT: Extras.score a A x ( Slots.att χ A u s ) =X:= perfect (scoreK hX hh) ht; unfold service; rw [hT]; refine tendsto_nhds_unique ?_ ( evaluate_full ht hX hh () i n ); refine Accord.select (f:=fun p:ℝ=> fun i n=> X i n () p []) (v:=Readings _ _ _ s q) ?_ i n; intro i n; obtain hs|hs:= i.eq_empty_or_nonempty
    · subst i; unfold Readings; dsimp only; rw [← show X=Slots.curve χ _ _ _ s from rfl ]; rw [ht.1]; exact ( Fleet.allow_zero _ ).1
    exact (Slots.verdict _ _ _ _ hh ht _ hs _).1 ()
omit [Fintype W] in
lemma symbolic (a:ℝ)(A:MS_Data G M)(u:W→Rake.Label b): Music a A u Smooth.Cruise.plain q= tour A u a q:= by
    rw [notation_t hp]; funext i n; exact Extras.tourC (fun i=> Extras.Estate ( safe _ _|>.2 ) ( safe _ _|>.1.1 ) _ ) ( touch hp ) u rfl i n
end YM.FVA2.DerivD

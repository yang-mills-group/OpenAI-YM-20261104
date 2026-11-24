import YM.FVAAlt2.Turn.Ocean
/-! commute motion with continuum MS `Joint` and `LPT` -> later covariance after rotations
use actual MINIMAL SUBTRACTION `Joint` with `Back` unchanged cone & frame. Never tacitly identify a lattice/MS patch. Keeping `leader` entirely unchanged (exploiting already true Sturdy). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Motions
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum Outlook
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge}{i:ℂ}{m n k:ℕ}{h x:ℝ}
variable (s:Spin (L 0))
local notation "B"=> motion G s
local notation "C"=> mcoat G s
local notation "X"=> mswing G s
variable {F H:Mob G}{J V W:Flats G}{K: Spin (L m)} {f g:Coat G} {t r:ℤ}
lemma motion_wind {I:Type} {l:Filter I}{T:I→Mob G}(he:Wind T l F): Wind ((B) ∘ T) l ( B F ):=by
   intro n w; let L:= flagS (s.arch (Nat.zero_le n)) G; exact Wind.center he _ (L.sense|>.reaches w)
lemma speed_mic {T:ℝ→ Rack G m}{A:Rack G m}(h:∀ i, HasDerivAt (fun x=> T x i) (A i) x) (u:Legs (Shore G m)): HasDerivAt (fun v=>beam (flagS K G) ( T v ) u) (beam (flagS K G) A u) x:= by
   induction u generalizing T A with | nil=> simpa using h []| cons y u ih=> simp_rw [Pilot.met]; exact HasDerivAt.fun_sum <| fun j _=> HasDerivAt.const_mul _ (ih (T:=fun i=>D (_, (flagS K G).volp y.2) ( T i )) (fun i=> h _)) -- ℝ field
lemma motion_speed {T:ℝ→Mob G} (h:speed T F x): speed ( (B) ∘ T ) ( B F ) x:= fun m i=> speed_mic (K:=s.arch _) (T:=fun i=> T i m) ( h m ) i
lemma motion_plow (a:ℂ)(t:ℝ)(F:Mob G): B (plow a t F)=plow a t ( B F ):= by
   funext n l; exact beam_W a t _ (F n) l
lemma motion_trail (h:Mell.Trail F H i): Mell.Trail ( B F ) ( B H ) i:= by constructor; intro t; simp_rw [← motion_plow]; exact motion_speed s ( h.derive t )
lemma motion_return (h:Return V f n): Return ( X V ) ( C f ) n:= by unfold Return; simp_rw [mzero,mco,← motion_plow]; exact h.mono (fun i hi=> motion_wind s hi)
lemma motion_page (y t:ℝ)(v:Flats G): Parade ( X v ) n y t=C ( Parade v n y t):= by
   let S:= ( X v ).support ∪ v.support; rw [Page S (by apply Finset.subset_union_left),Page S (by apply Finset.subset_union_right), map_sum]; refine sum_congr rfl fun i _=>?_ ; funext z; simp_rw [mzero,mco,hikeP, ← motion_plow,map_smul]
lemma motion_lift (h: Lift f F): Lift ( C f ) ( B F ):= by obtain ⟨T,r,hr,h,hf,hu⟩:=h; exact ⟨ _,r,hr,motion_hol s h,hf.mono (fun i hi=> congr_arg (B) hi),congr_arg (B) hu ⟩
lemma motion_live (h:Live f): Live ( C f ):= h.elim fun _ H=>⟨ _,motion_lift s H⟩
lemma motion_stay (h:Stay n V): Stay n ( X V ):=by intro y t; rw [motion_page]; exact motion_live s ( h y t )
lemma motion_mer (h:mer f): mer ( C f ):= by obtain ⟨n,h⟩:=h; refine ⟨n,?_⟩; unfold altitude; rw [ show paid n (C f) = C (paid n f) from funext fun t=> Eq.symm (map_smul (B) (t^n) (f t)) ]; exact motion_live s h
lemma motion_vibe (h:Vibe m J V): Vibe m (X J) ( X V ):= by apply h.mono; intro i hi k; simp_rw [mzero,mco]; exact motion_trail s ( hi _ )
lemma motion_cool (h: Cool f): Cool ( C f ):= by
   refine Submodule.span_induction (p:=fun f _=> Cool ( C f )) ?_ (by rw [map_zero]; exact (cone G).zero_mem) ?_ ?_ h; · rintro u ⟨v,hv,Q,rfl⟩; rw [show C (Ice v Q)=Ice v ( B Q ) from funext fun k=>map_smul (B) (k⁻¹^v) Q]; exact iceC _ _ hv
   · intro u v _ _ h h'; rw [map_add]; exact (cone G).add_mem h h'
   intro x v _ h; rw [map_smul]; exact (cone G).smul_mem _ h
lemma motion_count (h:Count f n): Count ( C f ) n:= fun _ x=> by rw [mco,← motion_plow,h _ x]
lemma motion_J (h:Joint n J V f g): Joint n (X J) (X V) (C f) (C g) := by
 refine ⟨motion_vibe s h.advance,motion_stay s h.toll,fun i=>?_, motion_cool s h.ice,motion_mer s h.worth,motion_count s h.back,?_⟩; · rw [mzero]; exact motion_mer s (h.wet _)
 rw [← map_add]; exact motion_return s h.sip
lemma motion_cap (h:Cap0 false t r f): Cap0 false t r ( C f ):= {
  fine:=⟨⟨motion_mer s h.fine.tune.mer,h.fine.tune.dice.mono fun _ H=>show Sturdy false _ from motion_sturdy s H ⟩, h.fine.ghost.mono (fun _ H=>show Collar t _ from motion_collar s H), ( show ∀ᶠ i:ℝ in realDotty,f i∈ sight G from h.fine.sense).mono fun i H=> show Sight _ from fun n l=> moves_sight (R:=f i n) (K:=s.arch _) l ((show Sight ( f i ) from H) n) ⟩
  cap:= h.cap.mono fun _ H=> show Issue r _ from fun n=> moves_rank (K:=s.arch _) ((show Issue r _ from H) n) }
lemma motion_sings (h:sings false t n f False J V g): sings false t n (C f) False (X J) (X V) (C g):= by
   obtain ⟨⟨r,hJ,hV,h⟩,_⟩:=h; obtain hp:= motion_J s hJ; rw [map_add] at hp; refine ⟨⟨r, hp.via ?_,fun i=>?_,motion_cap s h⟩,False.elim⟩; · exact common (fun _=> EventuallyEq.rfl) ( pact_X s (clockMoon hV) ( A_caps G 0 )) -- common name
   rw [mzero]; exact motion_cap s ( hV _ )
lemma pact_motion {U:Flats G}(h:Moony true U): Pact (X U) U:= by
   intro i; rw [mzero]; exact (sunny (h i)).mono fun k hk=> motion_trueS s hk.token
variable {K:T (Flats G)} {F V:T (Coat G)} {Hx:T (Flats G)} {xp q:T (Coat G)}
lemma platform_M (hp:leader G K F V) (v:T (Flats G)) (i:ℕ): Pact ( X (platform K i v) ) ( platform K i (( X ) ∘ v) ):= by
   unfold platform; rw [ map_sum ]; apply pact_sum _; intro i _; unfold drive0; rw [basis_tree s _ _ (A_caps G 0 |>.token) ( cl_a G 0 )]; exact pair_pact (A0 G 0) ( pact_motion s (clockMoon (gang (hp _)).price.choose_spec)) (fun _=> EventuallyEq.rfl) -- name
-- In particular `MS_Data` equivalent to the motion of itself from rotated Booked optics; uses its own independent unmarked and the same dimensions pole along this motion.
theorem motionM ( hp:leader G K F V)(he:comet n t K xp Hx q): comet n t K ((C) ∘ xp) (( X ) ∘ Hx) ((C) ∘ q):= fun i=> (motion_sings s (he i)).via ( platform_M s hp Hx i )
lemma press_stay (hh:Stay n J) : hereZ n (X J) x h=B (hereZ n J x h):= by apply Lift.unique (live0 (motion_stay s hh)); rw [motion_page]; exact motion_lift s ( live0 hh )
end YM.MS.FVA.Motions

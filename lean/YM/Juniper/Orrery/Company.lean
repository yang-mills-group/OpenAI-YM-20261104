import YM.Juniper.Orrery.Albedo
/-!
 # At top the E forecast starts from the WILSON STARTUP residual,
 explicit & genuine. Even under same folio fixing. Independent T.palette
 has those entries on every Side concluded below. Powers before earning
 a derivative for Tilt still to pay. Geometric estimates already done for
 Any Startup.Allows.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Org Pane Slide
open Progress.DirectedRecipe UVExtension Oriel Dales Tour Height Averaging
open Whirl Ovens Ovens.Pipes Rack Voucher Rain Time Bright Charted Lamppost Guild Tabernacle Spire
open WilsonStartup Start
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {c C f F:Side} {N m n k:ℕ} {ε:ℝ}
variable (P: BudgetPoint) (B:Clip) (β:ℝ)
local notation "T"=> WilsonStartup.Start.payload B P G c β
local notation "S"=> WilsonStartup.Start.dictionary G c
noncomputable def betaView (G:Gauge)(c:Side): Orrery.View G c:= ⟨(dictionary G c).reg,(payload B P G c β).regular⟩
abbrev skey (c : Side) := WilsonStartup.Key c
abbrev bkey (c:Side) : skey c ↪ ℕ:= ⟨fun j=> Padded.index (α:=Start.Sheet c) (.inl j),fun _i _j hk=> Sum.inl_injective (Padded.index_injective hk)⟩
abbrev betaset (c:Side): Finset ℕ:= Finset.map (bkey c) univ -- map clash
lemma visa (i:skey c) : (S).reg (bkey c i)= WilsonStartup.Key.addrE i:= by unfold dictionary; dsimp only; change eInfo (Padded.name _ (Padded.index (α:=Start.Sheet c) (.inl i)))=_; rw [Padded.name_index]; rfl
lemma earnsKey (i:skey c) : (payload B P G c β).regular (bkey c i)= written B (.inl i) β:= by
   change (if Padded.fixed (Start.Sheet c) (Padded.index (α:=Start.Sheet c) (.inl i)) then written B (Padded.name _ (Padded.index (α:=Start.Sheet c) (.inl i))) β else 0)=_; rw [Padded.name_index,if_pos (Padded.fixed_index _)]
lemma icon (i:skey C) : i.native=i.2.1:=rfl -- dot skey might fail
lemma beta_exists (i:ℕ) (h:(payload B P G c β).regular i ≠ 0): i∈ betaset c:= by
    simp only [Start.payload] at h; split at h; swap; · contradiction
    rename_i hz; cases e:Padded.name (Start.Sheet c) i with
    | inl j=> exact mem_map.mpr ⟨j,mem_univ _, ((congr_arg (Padded.index (α:=Start.Sheet c)) e.symm).trans (Padded.index_name hz))⟩
    | inr j=> rw [e] at h; exact (h rfl).elim
variable (he:2≤ P.B)
include he
lemma holdKey (i:ℕ)(h:i∈betaset c) : ShortF P.B ((S).reg i):= by obtain ⟨p,hp,rfl⟩:=mem_map.mp h; rw [visa]; intro j hj; apply (neighbors_mem ..).2; exact (WilsonStartup.Key.nearby p hj).trans he -- implicit G used in S; include B β unused?
lemma stationery : pod P (betaView P B β G c)=stampC (betaView P B β G c):= by
    let f:= betaView P B β G c; let K:= pod P f
    suffices h: K.E=f.field by exact congr_arg (fun u:ℕ→ Config G c→ℝ => { stampC f with E:=u }) h
    funext i; change (if ShortF P.B ((S).reg i) then (T).regular i else 0)= _; split; rfl
    rename_i h; exact (not_ne_iff.mp (mt (beta_exists P B β i (G:=G)) (fun h' => h (holdKey P he i h')))).symm
omit he
section era
variable (h:C.val=c.val*k)
local notation "q"=> Macrame.splitter (Deck.divides h)
local notation "A"=> Macrame.normal (Deck.divides h) h
abbrev goE (i:skey C) : skey c:= Prod.map id (Prod.map (Macrame.splitter (Deck.divides h)) id) i
include h in
lemma perch (i:skey C) : WilsonStartup.Key.skin (goE h i) = i.skin.image q :=by
   let x : Seat C:=(i.1,i.native); change (Meadow.pinch h x).spread (RG.touched (goE h i|>.root))=(x.spread (touched (i.root))).image q
   rw [show (goE h i).root=curr q i.root from Prod.ext (map_zero ..).symm rfl,Deck.touches_here h]; exact Orrery.spreaded h x _ -- curr names
include h in
lemma read_through (i:skey C)(x:Config G c) : (payload B P G C β).regular (bkey C i) ((A).links x)= (payload B P G c β).regular (bkey c (goE h i)) x:= by
    rw [earnsKey , earnsKey]; apply congr_arg (fun t => Start.weight B β * t)
    let y: Seat C:=(i.1,i.native); change WilsonStartup.Key.accrual i (A|>.links x)= WilsonStartup.Key.accrual (goE h i) x
    change WilsonStartup.residual G i.root (y.view ((A).links x))= WilsonStartup.residual G (goE h i).root ((Meadow.pinch h y).view x); unfold WilsonStartup.residual; rw [Meadow.estuary, Deck.mirror]; rw [show (goE h i).root=curr q i.root from Prod.ext (map_zero ..).symm rfl]
include h
local notation "U"=> betaView P B β G C
local notation "K"=> betaView P B β G c
lemma stencil_link : ∃ p:ℕ→ℕ, Leaves h p (U).root (U).field (K).root (K).field (betaset C) (betaset c):= by
    let u:= bkey C; let v:= bkey c; let p:= Function.extend u (fun i=> v (goE h i)) 0; have hV i : p (bkey C i)= bkey c (goE h i):= u.injective.extend_apply ..
    refine ⟨p,fun i hi=>?_,fun i hi=>?_,fun i hi=>?_,fun i x hi hx=>?_,fun i j hi hj hg hx=>?_⟩
    all_goals obtain ⟨i,hi,rfl⟩:=mem_map.mp hi
    · rw [hV]; refine ⟨mem_map_of_mem _ (mem_univ _),?_⟩; simp only [betaView,visa]; rfl
    · rw [hV]; simp only [betaView,visa]; exact perch h i
    · rw [hV]; intro x; exact read_through P B β h i x -- U config binder
    · let i':skey C:= (i.1,x,i.2.2); simp only [betaView,visa] at hx; refine ⟨u i',mem_map_of_mem _ (mem_univ _), (hV i').trans (congr_arg (v ·) (Prod.ext rfl (Prod.ext hx rfl))),?_⟩
      unfold u; simp only [betaView, visa]; rfl
    obtain ⟨j,hj,rfl⟩:=mem_map.mp hj; rw [hV,hV] at hx; apply congr_arg; have ht:= v.injective hx; simp only [betaView,visa] at hg; exact Prod.ext (congr_arg (fun x:skey c=> x.1) ht) (Prod.ext hg.symm (congr_arg (fun x:skey c=> x.2.2) ht))
end era
variable {L:Levels G} (ht: WilsonStartup.Start.Allows L N){d:ℝ}(hv:d∈band L N)
include ht hv
local notation "A"=> L.clock
local notation "ρ"=> (A).allowance N
local notation "W"=> (L.budget N)
local notation "t"=> (L.params N).clip
local notation "H"=> betaView W t d G c
local notation "F"=> stampC H
lemma boughtKey : (stampC H).Valid W ρ 0:= by
    let R':= Start.raw G c (t) (W) d; let U':= Pane.pale c G; have hf:= Pane.whey c G (W); have hb : R'.RegularFamily W:= Start.regularFamily d; have hv' : ‖d‖≤ 2*L.clock.hatBeta N:=by rw [Real.norm_of_nonneg ((show 0≤ L.clock.hatBeta N / 2 from half_pos (zero_lt_one.trans (L.fits.delayed _)) |>.le).trans hv.1)]; exact hv.2
    refine ⟨⟨hb.smooth,hb.at_flat,hb.vanish⟩,⟨hf.forced.sym,hf.forced.symtest,hf.forced.meas,hf.forced.meas_test,hf.forced.reads,hf.forced.reads_test,hf.forced.permit⟩,?_, Start.ink ht.radius ht.clip.direct hv' ht.income,hf.boundK⟩
    intro u s; let H':R'.Moves u s := (Start.moves ..).some; let h':= (hf.moves u s).some; exact ⟨⟨H'.ep,h'.kp,H'.reg_site,H'.reg_support,h'.forced_support,h'.forced_inventory,h'.forced_tests,H'.valuesE,h'.valuesK⟩⟩ -- nested?
include hv
noncomputable def prologue (u:ℝ)(h0:0≤u) : Canister G (L.budget N) (L.clock.allowance N) u:= by
    have he:=ht.clip.radius
    refine ⟨fun c=> betaView W t d G c, fun c (_:ℕ)=> betaset c,fun c _ i hi=>?_,fun c _ j i hi=> holdKey (G:=G) (W) he i hi, fun c C k h hx j=> stencil_link W t d h,fun c _=> Orrery.boughtKey ht hv,fun c _=>?_⟩
    · rw [stationery (W) t d he] at hi; exact Eventually.of_forall (fun _=> beta_exists W t d i (G:=G) hi)
    rw [stationery (W) t d he,sub_self]; refine ⟨0,fun i=> Progress.DirectedRecipe.no_cost ..,fun x=>?_⟩; simp [BudgetPoint.mass,SumBudget,h0]
end YM.Juniper.Orrery

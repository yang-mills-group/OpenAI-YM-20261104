import YM.MS.Rock.Glow
/-!
# Synchrony. Cost chords and scouting.

Across expansion support uniform orders. Need λ grammar. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Landau Arts Pilot Spin Arc Wire Path
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I A E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
   {b c:Bool}{m:ℕ}
lemma Sturdy0 : Sturdy b (0: Mob G) where
    grows _ _:=rfl
    turn _ _ _:= map_zero _
lemma Sturdy_plus {F H:Mob G}(h:Sturdy b F)(he:Sturdy b H): Sturdy b (F+H) where
    grows n i:= by simp only [Pi.add_apply,h.grows,he.grows]
    turn i K hK:= by rw [Pi.add_apply,map_add,h.turn i K hK, he.turn i K hK]
lemma Sturdy_scale {F:Mob G}(h: Sturdy b F)(x:ℂ): Sturdy b (x • F):= by
    refine ⟨fun i K hz=>?_ ,fun h' i=>?_⟩; · rw [Pi.smul_apply,map_smul,h.turn i K hz];
    simp only [Pi.smul_apply, h.grows h']
structure Sync (b:Bool)(f:ℂ→ Mob G): Prop where
    eye: Scout f
    vote:∀ i∈Town,Sturdy b (f i)
structure Stamp (b:Bool)(u: ℂ→ Rip G): Prop where
    arg: TrackR u
    tree: ∀ i∈Town,Ruddy b (u i)
-- lift Unit price
variable {f g:ℂ→ Mob G}{A B:ℝ}{z:UScale I}
lemma hills_add {D:Set ℂ} (h: Hol D f)(H: Hol D g): Hol D (f+g):=⟨fun c R hr he=> fall_add (h.price c R hr he) (H.price c R hr he),fun i p c hc=> DifferentiableAt.add (h.top i p c hc) (H.top i p c hc)⟩ -- replace shorthand
lemma shop_raise (h:Shine A f)(he:1≤A)(hp:A≤ B): Shine B f:= by intro m E _ _ _ w; exact (h m E w).raise (Cost.of_le fun i p _=> tall_mint he hp i)
lemma Sc_plux (h:Scout f)(H:Scout g): Scout (f+g):= by
    obtain ⟨A,hA,hF⟩:= h.price; obtain ⟨B,hB,hP⟩:= H.price; let V:=max A B; exact ⟨⟨V,le_max_of_le_left hA,fall_add (shop_raise hF hA (le_max_left ..)) (shop_raise hP hB (le_max_right ..))⟩,hills_add h.sky H.sky⟩
lemma around {h:E→F}(H: veg 0 (fun _:Unit=> h) 1): veg z (fun _:I=> h) 1:=by
   apply Arc.hike (fun _=> H.smooth ()); intro j; obtain ⟨C,hC,b,hb⟩:=Arc.ride H j; refine ⟨C,hC,b,fun i q=>(hb () q).trans ?_⟩; simp only [Pi.one_apply,Pi.zero_apply,abs_zero]; gcongr; exact abs_nonneg _
lemma arced {u:E→ F}(hu:rails 0 (fun _:Unit=>1) (fun _=>u)): rails z 1 (fun _=> u):= by
    intro b; refine ⟨fun _=> (hu b).smooth (), fun j=>?_⟩; obtain ⟨C,hC,l,hl⟩:= (hu b).quoted j; refine ⟨C,hC,l,fun i p hp=> (hl () p (mem_univ _)).trans ?_⟩; simp only [Arc.path,Scale.weight,mul_one,one_mul,Pi.zero_apply,Pi.one_apply,Scale.strict,abs_zero,one_pow]; gcongr; exact abs_nonneg _
variable {F:Mob G}{U:Rip G}
lemma travel (hf:kPrice F): fell z 1 (fun _=>F):= fun m E _ _ _ w=> around (hf m E w)
lemma transport (hv:rPrice U): rib z 1 (fun _=>U):= fun i a b=>arced (hv i a b)
lemma sncf (h:kPrice F)(hv:Sturdy b F): Sync b (fun _=> F):= by
   refine ⟨⟨⟨1,le_rfl,?_⟩,⟨fun c R hc hp=> travel h,fun m x z _=> differentiableAt_const _⟩⟩,fun _ _=>hv⟩; unfold Shine; rw [show mint 1=1 from funext (fun p:Town=>by simp [mint,LogMass])]; exact travel h -- mint not occur? Shine abbrev
lemma s_p (h:rPrice U)(hv:Ruddy b U): Stamp b (fun _=> U):= by
   refine ⟨⟨⟨1,le_rfl,?_⟩,⟨fun c R hc hp=> transport h,fun m a b p z hz=> differentiableAt_const _⟩⟩,fun _ _=>hv⟩; unfold Sugar; rw [show mint 1=1 from funext (fun p:Town=>by simp [mint,LogMass])]; exact transport h
lemma Sync.add (H:Sync b f)(h:Sync b g): Sync b (fun i=>f i+g i) := ⟨Sc_plux H.eye h.eye,fun i hi=> Sturdy_plus (H.vote i hi) (h.vote i hi)⟩
variable {u:ℂ→Rip G}
lemma Sync.ceil (h:Sync b f)(hz:Stamp b u)(hp : 1≤A)(ht:∀ i∈Town, rock A (u i)): Sync b fun i=>Path.ocean i (u i) (f i):= ⟨scouts_cycle h.eye hz.arg hz.tree h.vote hp ht, Rock.orbit h.eye hz.arg hz.tree h.vote hp ht⟩ -- name orbit
lemma Sync.drape (H:Sync b f)(hv:Sync b g)(hp:∀ n:ℕ,f n n= g n n){z}(hz:z∈Town): f z= g z:= by
   funext m l; refine agree_w (Dove H.eye m l) (Dove hv.eye m l) ?_ hz; filter_upwards [eventually_ge_atTop m] with n hn; rw [← (H.vote _ (Town_nat n)).grows hn, ← (hv.vote _ (Town_nat n)).grows hn,hp] -- hp ...
end YM.MS.Rock

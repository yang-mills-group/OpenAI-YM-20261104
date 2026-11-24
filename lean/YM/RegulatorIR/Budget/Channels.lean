import YM.RegulatorIR.Budget.RayPeriod

/-! Embedding fine and coarse species into the mixed joint alphabet. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Layer Motion Packet Tuple Deck
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y U V Z : Type} {r : ℕ} {P : ℝ}

namespace Packet
variable (f:X ↪ Y)

def acrossT (x:Tuple X r): Tuple Y r := f ∘ x
lemma injectT : Injective (acrossT (r:=r) f) := fun _ _ h=> funext fun i=> f.injective (congr_fun h i)
def crop (T:Packet Y r) : Packet X r:= T ∘ acrossT f
def offer (T:Packet X r):Packet Y r:= Stalk.collect (acrossT f) T
lemma offer_eq (T:Packet X r)(a: Tuple X r): offer f T (acrossT f a)= T a:=by
  unfold offer Stalk.collect
  apply tsum_eq_single (f:=fun z: Stalk (acrossT f) (acrossT f a)=>T z.val) (b:=⟨a,rfl⟩)
  intro i h; exact (h (Subtype.ext (injectT f i.property))).elim
lemma offer_zero {T:Packet X r}{x:Tuple Y r}(h:x∉ Set.range (acrossT f)) : offer f T x=0:=by
 unfold offer Stalk.collect; haveI : IsEmpty (Stalk (acrossT f) x) := ⟨fun z=>h ⟨z.val,z.property⟩⟩
 exact tsum_empty
lemma crop_symm (T:Packet Y r)(h:IsSym T): IsSym (crop f T):= fun e z=> h e (acrossT f z)
lemma offer_symm (T:Packet X r)(h:IsSym T): IsSym (offer f T):= by
 intro e p
 by_cases he:p∈Set.range (acrossT f)
 · obtain ⟨x,rfl⟩:=he
   rw [show acrossT f x ∘ e=acrossT f (x ∘ e) from rfl,offer_eq,offer_eq]; exact h ..
 rw [offer_zero f he,offer_zero]
 rintro ⟨x,hx⟩
 apply he; refine ⟨x ∘ e.symm,?_⟩; rw [show acrossT _ (x ∘ e.symm)=acrossT f x ∘ e.symm from rfl,hx,Function.comp_assoc,Equiv.self_comp_symm, Function.comp_id]

lemma mark_offer {T:Packet X r}{A:Tariff Z}{B:Premium A}{y:Y→Z}: markQ (B.uses y) (offer f T)≤markQ (B.uses (y ∘ f)) T := Stalk.quota_collect (acrossT f) T _
lemma mark_crop {T:Packet Y r}{A:Tariff Z}{B:Premium A}{y:Y→Z}: markQ (B.uses (y ∘ f)) (crop f T)≤markQ (B.uses y) T:= quota_restrict (acrossT f) (injectT f) T _

def customs (a:X)(i:Fin r): Hold i a ↪ Hold i (f a):= ⟨fun v=>⟨acrossT f v.val,congr_arg _ v.property⟩,fun _ _ h=>Subtype.ext (injectT f (Subtype.mk.inj h))⟩
lemma local_crop {T:Packet Y r}{A:Tariff Z}(y:Y→Z){c:ℝ≥0∞}(h:localQ (A.uses y) T c):localQ (A.uses (y ∘ f)) (crop f T) c:=fun i x=>(quota_restrict (customs f x i) (customs f x i).injective (fun z=>T z.val) (fun z=> (A.uses y).diameter z.val)).trans (h i (f x))
lemma local_offer {T:Packet X r}{A:Tariff Z}{y:Y→Z}{c:ℝ≥0∞}(h:localQ (A.uses (y ∘ f)) T c): localQ (A.uses y) (offer f T) c:=by
 intro i a
 by_cases hp : a∈Set.range f
 · obtain ⟨w,rfl⟩:=hp
   unfold Stalk.scopeQ quota; rw [← (customs f w i).injective.tsum_eq]
   · change (∑' z:Hold i w, ‖offer f T (acrossT f z.val)‖ₑ * _) ≤ _
     simp_rw [offer_eq]; exact h ..
   rintro ⟨z,hz⟩ he
   by_cases hw: z∈Set.range (acrossT f)
   · obtain ⟨u,rfl⟩:=hw; exact ⟨⟨u,f.injective hz⟩,rfl⟩
   exfalso; apply he; change ‖offer f T z‖ₑ*(A.uses y).diameter z =0; rw [offer_zero f hw]; simp
 apply le_trans (le_of_eq _) bot_le; unfold Stalk.scopeQ quota
 have ht (z:Hold i a):z.val∉Set.range (acrossT f):=by rintro ⟨v,h⟩;exact hp ⟨v i, (congr_fun h _).trans z.property⟩
 simp only [offer_zero f (ht _),enorm_zero,zero_mul,tsum_zero, ENNReal.bot_eq_zero]
end Packet

/-- Saturated species leg, with aligned choice of positive-link representatives.
The position identity is in *physical* coordinates even on mixed precision. -/
structure Channel (A:Deck P X U)(B:Deck P Y V) where
 native : X ↪ Y
 tile : U ↪ V
 car (d i): native (A.wind d i) = B.wind d (native i)
 project x : B.orbit (native x)=tile (A.orbit x)
 picks u : B.place (tile u)=native (A.place u)
 position x : B.pos (native x)= A.pos x
 paint x : B.orient (native x)=A.orient x
namespace Channel
variable {A:Deck P X U}{B:Deck P Y V}(t:Channel A B)

lemma aboard {x:Y}{u:U}(h:B.orbit x=t.tile u) : ∃ i:X, t.native i=x := by
 obtain ⟨v,hv,-⟩:=B.edges (B.place (t.tile u)) x ((B.placed ..).trans h.symm)
 rw [t.picks] at hv
 exact ⟨_,(t.car v (A.place u)).trans hv⟩
lemma across_orbit (x:Tuple X r): B.project (acrossT t.native x)=acrossT t.tile (A.project x):=funext (fun i=> t.project (x i))
lemma pigment (x:Tuple X r) : B.polish (acrossT t.native x)=A.polish x:= Finset.prod_congr rfl fun _ _=> t.paint _
lemma crop_valid {T:Packet Y r}(h:B.Ready T):A.Ready (crop t.native T):=by
 apply (A.ready_iff _).mpr
 intro d x; unfold crop
 rw [Function.comp_apply, show acrossT t.native (A.wind d∘ x)= B.wind d ∘ acrossT t.native x from funext (fun i=> t.car d (x i)),(B.ready_iff _).mp h]; rfl
lemma offer_valid {T:Packet X r}(h:A.Ready T) : B.Ready (offer t.native T):=by
 apply (B.ready_iff _).mpr;intro d x
 by_cases hv:x∈Set.range (acrossT t.native)
 · obtain ⟨z,rfl⟩:=hv
   rw [show B.wind d ∘ acrossT t.native z=acrossT t.native (A.wind d ∘ z) from funext (fun i=>(t.car d (z i)).symm),offer_eq,offer_eq]; exact (A.ready_iff _).mp h ..
 rw [offer_zero _ hv,offer_zero,mul_zero]
 rintro ⟨z,h⟩;apply hv
 refine ⟨A.wind (undo d) ∘ z,?_⟩;ext1 i
 change t.native (A.wind _ (z i))=_;rw [t.car,show t.native (z i)=_ from congr_fun h i,B.reversed]; exact Equiv.symm_apply_apply ..
lemma native_paid : B.pos ∘ t.native=A.pos:= funext t.position
lemma tile_paid : B.atO ∘ t.tile=A.atO:=by funext u; exact (congr_arg B.pos (t.picks u)).trans (t.position _)
end Channel
end YM.RegulatorIR.Budget

namespace YM.RegulatorIR.Budget
open Function Packet Tuple Deck Motion
open scoped Topology ENNReal NNReal BigOperators Classical
namespace Channel
variable {X Y U V : Type}{r:ℕ}{P:ℝ}{A:Deck P X U}{B:Deck P Y V}(t:Channel A B)

def tunnel (v:Tuple U r):Stalk A.project v≃Stalk B.project (acrossT t.tile v):=by
 refine Equiv.ofBijective (fun z=>⟨acrossT t.native z.val,(t.across_orbit ..).trans (congr_arg _ z.property)⟩) ⟨fun a b h=>Subtype.ext (injectT _ (congr_arg Subtype.val h)),?_⟩
 intro u
 have h (i:Fin r) : ∃ x:X,t.native x=u.val i := t.aboard (show B.orbit (u.val i)=t.tile (v i) from congr_fun u.property i)
 choose x hx using h
 have he : acrossT t.native x= u.val:=funext hx
 have h' := injectT t.tile (((across_orbit t x).symm.trans (congr_arg B.project he)).trans u.property)
 exact ⟨⟨x,h'⟩,Subtype.ext he⟩

def drill (v:Tuple U r) (x:X) (i): Nest A v i x≃Nest B (acrossT t.tile v) i (t.native x) := by
 refine Equiv.ofBijective (fun z=>⟨acrossT t.native z.val,(t.across_orbit ..).trans (congr_arg _ z.property.1),congr_arg t.native z.property.2⟩) ⟨fun a b h=>Subtype.ext (injectT _ (congr_arg Subtype.val h)),?_⟩
 intro u
 obtain ⟨w,hw⟩:=(t.tunnel v).surjective ⟨u.val,u.property.1⟩
 have hh: acrossT t.native w.val=u.val:= congr_arg Subtype.val hw
 have h:t.native (w.val i)=t.native x:=(congr_fun hh i).trans u.property.2
 exact ⟨⟨w.val,w.property,t.native.injective h⟩,Subtype.ext hh⟩

lemma lodge_crop (T:Packet Y r) v x i : A.lodge (crop t.native T) v i x=B.lodge T (acrossT t.tile v) i (t.native x) := by
 unfold lodge; rw [← (t.drill v x i).tsum_eq]; apply tsum_congr; intro z
 exact congr_arg (T (acrossT t.native z.val) * ·) (t.pigment z.val).symm
lemma crop_project (T:Packet Y r) : A.deckSum (crop t.native T) = crop t.tile (B.deckSum T):=by
 ext1 v; change A.deckSum _ v=B.deckSum _ (acrossT t.tile v); unfold deckSum; split
 · rw [lodge_crop,picks']
 rfl
where
 picks' (v:Tuple U r) (i) : B.place (acrossT t.tile v i)=t.native (A.place (v i)):= t.picks _
lemma crop_scroll (T:Packet Y r) : A.scroll (crop t.native T) = crop t.tile (B.scroll T):=by
 ext1 v;change A.scroll _ v=B.scroll _ (acrossT t.tile v); unfold scroll Stalk.collect; rw [← (t.tunnel v).tsum_eq]; apply tsum_congr;intro x
 exact congr_arg (T (acrossT t.native x.val) * ·) (t.pigment x.val).symm
lemma dyed_offer_zero (T:Packet X r) {u:Tuple V r} (h:u∉ Set.range (acrossT t.tile)) (z:Tuple Y r)(hz:B.project z=u):B.dyed (offer t.native T) z=0 := by
 rw [dyed,offer_zero,zero_mul];rintro ⟨v,rfl⟩;exact h ⟨A.project v,(t.across_orbit v).symm.trans hz⟩
lemma offer_project (T:Packet X r) : B.deckSum (offer t.native T)=offer t.tile (A.deckSum T):=by
 ext1 v
 by_cases h:v∈Set.range (acrossT t.tile)
 · obtain ⟨u,rfl⟩:=h; rw [offer_eq]; nth_rw 2 [← show crop t.native (offer t.native T)=T from funext (offer_eq t.native T)]
   rw [crop_project]; rfl
 rw [offer_zero _ h]; unfold deckSum; split
 next hv =>
    unfold lodge
    simp_rw [fun (x : Nest B v (⟨0,hv⟩:Fin r) (B.place (v ⟨0,hv⟩))) => t.dyed_offer_zero T h x.val x.property.1]
    exact tsum_zero
 rfl
lemma offer_scroll (T:Packet X r) : B.scroll (offer t.native T)=offer t.tile (A.scroll T):=by
 ext1 v; by_cases h:v∈Set.range (acrossT t.tile)
 · obtain ⟨u,rfl⟩:=h;rw [offer_eq]; nth_rw 2 [← show crop t.native (offer t.native T)=T from funext (offer_eq t.native T)]; rw [crop_scroll];rfl
 rw [offer_zero _ h]; unfold scroll Stalk.collect; simp_rw [fun x:Stalk B.project v=> t.dyed_offer_zero T h x.val x.property]; exact tsum_zero
end Channel
end YM.RegulatorIR.Budget

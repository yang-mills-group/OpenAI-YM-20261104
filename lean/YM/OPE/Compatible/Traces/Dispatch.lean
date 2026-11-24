import YM.OPE.Compatible.Traces.Incoming
/-!
# Handshake commission

Generic rightward purchases (already know precisely which Lines the
charges are taken from), still preserving the lifetime forecasts
for survivors. At a nonSolo can choose in another lemma a signed
pair-run at appropriate grade instead of this leader. Here regular.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi
open scoped Topology Classical
variable {G:Gauge} {C:Family G}(A:Allot C){V I J Z :Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
    [Fintype J][DecidableEq J] [Fintype Z][DecidableEq Z](P:Ensemble V)
variable {N p i b H l:ℕ}
namespace Lights
variable {F:Fibers (I⊕Z) J}{o:I→Track C.path V p} {o':J→Track C.path V p}
    {A P} {E:Track C.path V p} {k:I→ℕ}{k' j:J→ℕ}
    (L:Lights A P N p k (i+1) b E o)
-- damper
variable (C) in
def valve (H b l i:ℕ):ℝ:= min 1 ((license C.path (renal C.path.levels) H l i) / (β C (i+1))^b)
lemma valve_pos (C:Family G)(A:Allot C) (b l:ℕ)(h:0<H)(hp:C.ref 0 ≤ i): 0< valve C H b l i:= lt_min zero_lt_one (div_pos (license_pos _ _ (A.arcPars hp).funs.1 h) (pow_pos (β_pos ..) _))
variable {B₀:Nat}
-- new leaving facts. If not provide counters. mark port.
structure Bind (C:Family G)(P:Ensemble V){p:ℕ}(E:Track C.path V p)(F:Fibers (I⊕Z) J)(o:I→Track C.path V p)(o':J→Track C.path V p)(i:ℕ)(k:I→ℕ) (k' j:J→ℕ) : Prop where
    fell a : k a ≤ i -- need last hop, important
    elder x : F.SingleFiber x → ∃ a,F.twig x=.inl a ∧ k a=k' x∧o a=o' x
    keep x : ¬ F.SingleFiber x → C.ref 0 < k' x
    ahead x : ¬ F.SingleFiber x → k' x ≤ j x ∧ j x ≤ i
    pins x : ¬ F.SingleFiber x → Migrating C.path (j x) p i (o' x)
    parents x : ¬ F.SingleFiber x → ∀ t,k' x≤ t→ t < i → (C.path.levels.clock.op t p).ratio.parent ∘ o' x (t+1)=o' x t
    periods x : ¬ F.SingleFiber x → Migrating C.path (k' x) p i E
    authorized x : ∀ m,k' x ≤ m → m ≤ i→∀ a,a≠P.v → o' x m a= affine (P.move a).1 (E m a) (o' x m P.v) -- needs even solo
    embers a : ¬ F.SingleFiber (F.bunch (.inl a)) → k a=i
section
set_option quotPrecheck false
local notation "T"=> grouped C.path (renal C.path.levels) H l i (Sum.elim L.asks (1:Z→ℝ)) F
-- costly geom. expose survivors' all times and Stamps retained for counter merge.
structure Issues (l H:ℕ) (F:Fibers (I⊕Z) J)(S:Lights A P N p k' i b E o')(j:J→ℕ) :Prop where
    inherited x : F.SingleFiber x → ∀ a,F.twig x=.inl a→
      (S x).X=(L a).X ∧ ∀ t, (S x).w t= valve C H b l i *(L a).w t
    fresh x : ¬ F.SingleFiber x → S.bottom x= Run.Below C.path ((sash C i)* (grouped C.path (renal C.path.levels) H l i (Sum.elim L.asks 1) F x)/2) (j x) (k' x)
    blades x : ¬ F.SingleFiber x → let X:= S.tips x; let v:=S.asks x; Blade (C.path.rep N p i) (X.home P.v) (X.oil P.v) (profile (C.path.rep N p i).activities (X.gas P.v)) 0 (4*(1/v))
variable (M:Bind C P E F o o' i k k' j) (U:J→Stem V G (C.S.side i p))
include M
lemma commission (hg:G.Simple)(hC:C.Makes)(hn:i ≤ N)(ht:0<H)(hR:C.ref 0 < i)
    (hp:∀ a: J,(U a).home=o' a i)(hb:∀ a: J,Marked (C.path.rep N p i) (E i) P (U a))(hy:∀ a:J,F.SingleFiber a → ∀ x:I,F.twig a=.inl x → U a=(L x).X i)
    (hh:∀ a:J, ¬ F.SingleFiber a→ Blade (C.path.rep N p i) ((U a).home P.v) ((U a).oil P.v) (profile (C.path.rep N p i).activities ((U a).gas P.v)) 0 (4*(1/T a))) :
    ∃ S:Lights A P N p k' i b E o', (∀ a, (S a).X i=U a) ∧ S.asks ≤ T ∧ Issues L l H F S j:=by
    let α:=valve C H b l i; let w:=grouped C.path (renal C.path.levels) H l i (Sum.elim L.asks (1:Z→ℝ)) F
    have hw a:0<w a:=grouped_pos H l F (A.arcPars hR.le).funs.1 ht (fun x=> by cases x; exact L.asks_pos _; exact zero_lt_one) _
    have he:0<α:=valve_pos C A b l ht hR.le
    have h(a:J):∃ V': Line A P N p (k' a) i b E (o' a),V'.X i=U a∧ V'.w i≤ w a∧ (F.SingleFiber a → ∀ x:I,F.twig a=.inl x→V'.X=(L x).X ∧ ∀ t,V'.w t=α*(L x).w t) ∧ (¬F.SingleFiber a→ V'.w (k' a)=Run.Below C.path (sash C i*w a /2) (j a) (k' a) ∧ Blade (C.path.rep N p i) ((V'.X i).home P.v) ((V'.X i).oil P.v) (profile (C.path.rep N p i).activities ((V'.X i).gas P.v)) 0 (4*(1/(V'.w i)))):=by
       by_cases hv:F.SingleFiber a
       · obtain ⟨x,hx,hE,hU⟩:= M.elder a hv
         let L':= ((L x).cut (M.fell x) i.le_succ).damp α he (min_le_left ..)
         rw [← hE,← hU]
         refine ⟨L',(hy a hv x hx).symm,?_,fun _ i hi=>?_, fun h=>False.elim (h hv)⟩
         · have hg:(L x).w i ≤ L.asks x*β C (i+1)^b:= (L x).guard' i (M.fell x) i.lt_succ_self
           let δ:= license C.path (renal C.path.levels) H l i; have hL: w a=δ*L.asks x:= by unfold w grouped; rw [hv,Finset.prod_singleton,hx]; rfl
           rw [hL]; refine (mul_le_mul_of_nonneg_left hg he.le).trans ?_
           let p:= β C (i+1)^b; have ht:0<p:=pow_pos (β_pos ..) _; have h:= (le_div_iff₀ ht).1 (show α ≤ δ / p from min_le_right ..)
           refine le_trans ?_ (mul_le_mul_of_nonneg_right h (L.asks_pos x|>.le)); exact le_of_eq (by unfold p; ring)
         obtain rfl:x=i:= Sum.inl.inj (hx.symm.trans hi); exact ⟨rfl,fun _=>rfl⟩
       obtain ⟨G,hZ,hT,hA,hI⟩:= new_line A P (b:=b) hg hC (M.keep a hv) (M.ahead a hv).1 (M.ahead a hv).2 hn (M.periods a hv) (M.pins a hv) (M.parents a hv) (M.authorized a) (hw _) (hp a) (hb a) (hh a hv)
       refine ⟨G,hZ,hA,fun he=>False.elim (hv he),fun _=>⟨hI,hZ ▸ Blade.more (hh a hv) ?_⟩⟩
       exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (G.hold.fees i G.hold.clock le_rfl) hA) (by norm_num)
    choose U he hz hp hs using h
    exact ⟨U,he,hz,hp,fun i h=> (hs i h).1,fun i h=>(hs i h).2⟩
end
end Lights
end YM.OPE.Allot

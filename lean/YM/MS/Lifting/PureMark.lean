import YM.MS.Lifting.Born
/-!
# Leading fits on stencils

fieldDim weight, zero for larger ranks only by explicit rank mask.
Normalize highest rank (before free self contractions). Lower rank outputs
 could be normalized separately with same algorithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Wire Tensor Book
open Landau Detect Detect.Mark Cylinder Lab Taylor Native Draft Paint Sew Native.Chart Orient Wilsonian Studio
open Tone Tone.Frame Lattice Local Local.BV Submodule
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F S:Dot G Cover}{v u:ℤ}{H K:Law G} {n q:ℕ}{b:Bool}
def Fits (F:Dot G Cover)(H:Law G)(n:ℕ)(h:ℤ)(b:Bool): Prop:= Face wfield (Book.mask n (Tone.run F)) H h b -- Face ambiguous
namespace Fits
lemma add (h:Fits F H n v b)(he:Fits S K n v b): Fits (F+S) (H+K) n v b:= by unfold Fits; rw [map_add,map_add]; exact face_add h he
lemma smul (p:ℂ)(h:Fits F H n v b): Fits (p • F) (p • H) n v b:= by unfold Fits; rw [map_smul,map_smul]; exact face_mul p h
lemma sum {A:Type}{F:A→Dot G Cover}{H:A→Law G}(J:Finset A) (h:∀ j∈J,Fits (F j) (H j) n v b): Fits (∑ j∈J,F j) (∑ j∈J,H j) n v b:= by unfold Fits; rw [map_sum,map_sum]; exact face_sum h
lemma zero (v:ℤ): Fits (G:=G) 0 0 n v b:= by unfold Fits; rw [map_zero,map_zero]; exact face_zero v
lemma From_run (h:From F.val v): From (run F) v:= by
   intro l he; rw [← enough l (F:=run F) (show (l.length:ℤ)=l.length from rfl),← Tone.grade]; have hz : model (l.length:ℤ) F=0:= by apply Subtype.ext; ext k; by_cases hx:(k.length:ℤ)=l.length; exact (enough k hx).trans (h k (by omega)); exact strange _ hx
   rw [hz,map_zero]; rfl
lemma take (h:Fits F H n v false)(hh:Fits S K q u false)(hv:From F.val n)(hq:From S.val q): Fits (couple DotFlip F S) (product DotFlip H K) (n+q) (v+u) false:= by
   unfold Fits; rw [wave_cost, Nat.cast_add]; let ζ := (pairLevel (p:=DotFlip) 0 (From_run hv) (From_run hq)); simp only [Finset.Nat.antidiagonal_zero,Finset.sum_singleton,rankLevel,Nat.cast_zero,zero_add] at ζ; rw [←ζ]; exact face_product h hh
lemma rank1 (f:Grade G)(h:∀ a:Branch G Axis, ∀ p:QP, Rest (fun t:ℝ=> run F [(a,t • p)]) (v-wfield a) (f (a,p))): Fits F (Koszul.mono f) 1 v false:= by
   intro l hl; by_cases ht : l.length=1; · obtain ⟨⟨j,p⟩, rfl⟩:= List.length_eq_one_iff.mp ht; unfold fieldVal; simp only [ray_go,List.map_cons,List.map_nil]; simp only [Book.mask]; simp; exact h j p
   rw [show fieldVal _ (ray l)=fun _=> (0:ℂ) from funext fun i=> strange _ (by rw [sail_len,ray_len]; omega),grade1 f l (by rw [mod_int]; omega)]; exact Rest.zero _
lemma unit : Fits (G:=G) (piece 1) (coin 1) 0 0 b:= by
    have h : rank 0 (coin (1:ℂ):Law G):= by rintro (_|i) H; apply False.elim (H rfl); rfl
    unfold Fits; rw [show run (G:=G) (piece 1)=coin 1 from coin_turn ..,Nat.cast_zero, (rank_hat _|>.mp h)]; intro w hw; cases w with | nil=> exact Rest.level contDiff_const rfl| cons i w=> exact Rest.zero _
end Fits
lemma path_in (L:Plaq)(i:CI G): Fits (ropeV idRail L 0 i) (Koszul.mono (L.mark i)) 1 L.value false:= Fits.rank1 _ (rope_rest L i)
lemma mon_F (n:ℕ)(f:Fin n→ Plaq)(u:Grid G n): Fits (monV idRail 0 n f u) (family n (Plaq.mark∘f) u) n (∑ i,(f i).value) false:= by
    induction n with
    | zero=> rw [Fin.sum_univ_zero]; exact Fits.unit
    | succ n ih=> rw [Fin.sum_univ_succ]; let X:= (path_in (f 0) (u 0)).take (ih (f ∘ Fin.succ) (u ∘ Fin.succ)) (ropeCheap idRail (f 0) 0 (u 0)) (mon_L idRail 0 n (f ∘ Fin.succ) (u ∘ Fin.succ)); rw [add_comm 1 n] at X; exact X
lemma mark_F (n:ℕ)(f:Fin n→ Plaq)(u:Grid G n): Fits (markP n f u) (breeze (family n (Plaq.mark∘f)) u) n (∑ i,(f i).value) false:= Fits.sum _ (fun i _=> (mon_F _ _ i).smul _)
-- Runtime label at arity n. Need cohom basis choice. Coeff y later.
lemma liftP (h:H∈ Physical.Allowed G v n): ∃ F:Dot G Cover, Aura F n ∧ Fits F H n v false:= by
   refine span_induction (p:=fun H _=> ∃ F, Aura F n ∧ Fits F H n v false) ?_ ⟨0,Aura.zero _ _,Fits.zero _⟩ ?_ ?_ (syntaxK h)
   · rintro x ⟨u,w,rfl,he,rfl⟩; exact ⟨_,real_A ..,mark_F n u w⟩
   · rintro u v hv hu ⟨k,hk,he⟩ ⟨q,hq,hf⟩; exact ⟨k+q,hk.add hq,he.add hf⟩
   rintro c f h ⟨p,H,hp⟩; exact ⟨(c:ℂ) • p,H.scalar c,hp.smul (c:ℂ)⟩
end YM.MS.Lifting

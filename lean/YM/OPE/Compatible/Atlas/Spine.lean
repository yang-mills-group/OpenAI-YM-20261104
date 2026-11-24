import YM.OPE.Compatible.Atlas.TreeCast
/-! evaluates through live hierarchy rather than extrapolate Cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V J I:Type}[PartialOrder X][OrderBot X][Fintype X][Fintype J][Fintype I]
   (D:Origin X){Q:Finset X}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
variable {ψ:Filter V}{T: V→ℝ} {s: V→X→ℝ}(r:V→Viewers U)(y:V→ J→E4)(p:I→ C.book.Token)(q:J→ C.book.Token)
-- for every cast, wings open. actual copies roots internal.
variable {z:I→X}(H: Burst D Q ψ T s) {η M c:ℝ}
include H
lemma clear_shifted (hR:Row D (Q:=Q) z) (hc:0<c)(hy:∀ᶠ i in ψ,ClearOf 0 (y i) c)(hη:0<η)(a:X)(ha:a∈allUp D Q):∀ᶠ i in ψ,∀ x:X→ E4,Ridge (s i) η M D Q x→ Injective (beside (OPE.away (x∘z) (x a)) (y i)) :=by
    filter_upwards [enough D H (M:=M) (show 0<c/3 by positivity) hη,hy,(time_bright D (H.fresh _ hη)).lit] with i ⟨h,hq,hw⟩ hy hs x hx
    apply beside_distinct.mpr; refine ⟨(away_inject ..).2 ?_,(beside_distinct.mp (hy.inject_both hc)).2.1,?_⟩
    · intro u v h; by_contra ha; have hu:= hR.spaced u v ha; have he:= hx.span _ _ (hR.active u) (hR.active v) hu (hR.spaced v u (Ne.symm ha))
      change x (z u)=x (z v) at h; have hv:= (mul_pos hη (hs.pos _ (diverge D (Burst.crown D H) (hR.active u) hu))).trans_le he; rw [h,sub_self,norm_zero] at hv; exact lt_irrefl _ hv
    intro u v h; have hp: ‖x (z u)-x a‖ ≤ c/3+c/3 := (norm_sub_le ..).trans (add_le_add (hw x hx _ (hR.active u)) (hw x hx _ ha)); change x (z u)-x a=y i v at h; rw [h] at hp; have he:=hy.openSpace v; rw [zero_sub,norm_neg] at he; linarith only [hc,hp,he]
lemma to_spectra (hR:Row D (Q:=Q) z)(P:Prescription U.sector.derivatives)(hη:0<η)(a:X)(ha:a∈allUp D Q)(w:Mode U.sector.derivatives): Scannable U D Q ψ T s η M 2 (fun _ x=> P.ope w (x∘z) p (x a)):=by
   let B(e:Exterior C.book) (i:V)(x:X→E4):= (P.sheet w) e * Prescription.reading S (x∘z) p (x a) e; refine Scannable.summons D _ B (fun e he=>?_)
   unfold B; refine Scannable.mul D (Scannable.constant D _) ?_; obtain ⟨u,hu,hc⟩:= cleared e
   let y(_:V):= bearing e; let q:= e.letter; have hY : ∀ᶠ i in ψ, ClearOf 0 (y i) u:=Eventually.of_forall (fun i=> hc)
   refine Scannable.shift D (cast_item D (M:=M) (fun _=> none) y p q H hR hu hY hη a ha) ?_
   filter_upwards [clear_shifted D y H (M:=M) hR hu hY hη a ha] with i hi x h; specialize hi x h
   let A:= beside (away (x∘z) (x a)) (bearing e); let V:= beside p q; have he:= observe_carry S U.room.kernel.translations (x:=A) V hi (x a)
   rw [show (fun i=>A i+x a)=beside (x∘z) (fun j=>x a+y i j) from funext fun j=> by cases j <;>simp [A,away,y,add_comm (x a)]] at he
   unfold Prescription.reading; dsimp only; rw [if_pos (by exact hi)]; exact he
omit H in
lemma row_one (v:X)(hv:v∈allUp D Q) : Row D (Q:=Q) (sole v):= ⟨fun _=>hv,fun _ _ hi=> False.elim (hi (Subsingleton.elim ..))⟩
lemma truncated_cast (hR:Row D (Q:=Q) z)(P:Prescription U.sector.derivatives)(n:ℕ)(hc:0<c)(hy:∀ᶠ i in ψ, ClearOf 0 (y i) c) (hη:0<η): Scannable U D Q ψ T s η M 2 (fun i x=> P.truncated (spectator U (r i)) n (x∘z) p 0 (y i) q):=by
    let v(w) (i:V)(x:X→E4):= P.termRead (spectator U (r i)) (x∘z) p 0 w (y i) q; have hh:⊥∈allUp D Q:= Finset.mem_union_left _ (Burst.crown D H|>.base)
    refine Scannable.summons D _ v fun i hi=> ?_; refine Scannable.shift D (Scannable.mul D (to_spectra D p H hR P (M:=M) hη _ hh i)
       (cast_item D r y (sole (P.letter i)) q H (row_one D _ hh) hc hy hη _ hh)) (Eventually.of_forall (fun j x hx=>?_))
    unfold v Prescription.termRead; rw [hx.belly,show x∘ sole ⊥=sole 0 from funext fun _=>hx.belly]; simp
lemma row_root : Row D (Q:=Q) (Subtype.val : brim D Q→ X):= ⟨fun i=>Finset.mem_union_right _ i.2,fun i j hi=>brim_apart D Q (Burst.crown D H) i.2 j.2 (Subtype.val_injective.ne hi)⟩
lemma root_cast (q':brim D Q→ C.book.Token)(P:Prescription U.sector.derivatives)(w:Mode U.sector.derivatives)(hη:0<η): Scannable U D Q ψ T s η M 2 (fun _ x=> P.ope w (picked _ x) q' 0) :=
    Scannable.shift D (to_spectra D q' H (row_root D H) P hη _ (Finset.mem_union_left _ (Burst.crown D H).base) w) (Eventually.of_forall fun _ _ h=> congr_arg _ h.belly)
lemma total_cast (q':brim D Q→ C.book.Token)(P:Prescription U.sector.derivatives)(n:ℕ)(hc:0<c)(hy:∀ᶠ i in ψ, ClearOf 0 (y i) c) (hη:0<η): Scannable U D Q ψ T s η M 2 (fun i x=> observe (spectator U (r i)) (beside (picked _ x) (y i)) (beside q' q) - P.truncated (spectator U (r i)) n (picked _ x) q' 0 (y i) q):=by
    refine Scannable.sub D (a:=fun i x=>observe (spectator U (r i)) (beside (picked _ x) (y i)) (beside q' q)) ?_ (truncated_cast D r y q' q H (row_root D H) P n hc hy hη)
    refine Scannable.shift D (cast_item D r y q' q H (row_root D H) hc hy hη _ (Finset.mem_union_left _ (Burst.crown D H).base)) (Eventually.of_forall fun i x h=>?_)
    simp_rw [h.belly,zero_add,picked]
end YM.OPE.Arboreal.Trace

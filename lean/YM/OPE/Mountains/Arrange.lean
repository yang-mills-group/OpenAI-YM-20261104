import YM.OPE.Beams.Epoch
import YM.OPE.Trees.Prior
import YM.OPE.Exchange.Coherence
import YM.OPE.Mountains.Portrait
/-!
# Erase and restore companion names in an Active offer

For arbitrary focuses under the tree. The price convention sees only
actual positions; we move into a relative-coordinate frame for applying
the sign theorem. Relabel the actual horizon charge and same `ope`.
Unit (when a border vertex has empty input) also gives an exact step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Mountain
open Function Filter Finset OPE.Log Trunk Reels Log.Trunk.Shuttle
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S) (P:Prescription U.sector.derivatives)
variable {I J:Type}[Fintype I] {s:Arboreal I} {f:Filter J} {t:I→ℝ} {x:J→I→E4}{R:J→I→ℝ}
    (X:I→E4){M δ:ℝ}{i j k o u:I} {a b : Finset I} (p:I→ C.book.Token) (d:ℕ) (w:Mode U.sector.derivatives)
local notation "I'"=> (↑(s.live a):Type)
local notation "C'"=> (↑(s.external a i):Type)
local notation "A'"=> (↑(s.inputs a i):Type)
local notation "Z!"=> (↑(s.live (s.redact a i)):Type)
local notation "X'"=> (crop X (s.live a))
-- gates etc
-- compare chunk slots
private def roll {q:Finset (↑a:Type)} (h:b⊆a)(h':∀ i:(↑a:Type),i∈q↔ i.val∈b): (↑q:Type) ≃ (↑b:Type):=
    ⟨fun i=>⟨i.val.val,(h' _).1 i.property⟩,fun i=>⟨⟨i.val,h i.property⟩,(h' _).2 i.property⟩,fun _=>rfl,fun _=>rfl⟩
private def red (hi:i∉ a)(he:b=insert i a) : (Unit⊕(↑a:Type)) ≃ (↑b:Type):= (((Equiv.sumCongr (show Unit≃(↑({i}:Finset I):Type) from ⟨fun _=> ⟨i,mem_singleton_self _⟩,fun _=>(),fun _=>rfl,fun u=> by refine Subtype.ext ?_; exact (mem_singleton.mp u.property).symm⟩) (Equiv.refl _)).trans (Equiv.Finset.union _ _ (disjoint_singleton_left.mpr hi))).trans (Equiv.setCongr (show (({i}∪a : Finset I) : Set I)=(b:Set I) from (by rw [singleton_union,he]))))
private lemma wheel {V:Type*}(x:I→V)(hi:i∉a)(he:b=insert i a): crop x b ∘ red hi he=beside (sole (x i)) (crop x a):= by funext i; cases i<;> rfl
private lemma hwheel {V:Type*}(x:I→V)(v:V)(hi:i∉a)(he:b=insert i a): crop (update x i v) b ∘ red hi he=beside (sole v) (crop x a):=by
    rw [wheel, update_self, show crop (update x i v) a=crop x a from funext (fun j=> update_of_ne (show j.val ≠ i from fun h=>hi (h ▸ j.property)) v x)]

variable (H:s.Active a)(hy:i∈s.middle a) {q:Finset (↑(s.live a):Type)}
    (hp:∀ j:(↑(s.live a):Type),j∈q↔ j.val∈s.inputs a i)
include U H hy
lemma redact_token (z:C.book.Token)(o:I) :
    P.ope w (beside (sole (X i)) (crop X (s.external a i))) (beside (sole z) (crop p (s.external a i))) (X o)=coalesce P (s.live (s.redact a i)) X (update p i z) o w:=by
    let V:= U.room.kernel.laws.toSymmetric; let e : (Unit⊕C')≃Z! := red (no_shadow s i a) (pruned H hy)
    let V':=crop (update p i z) (s.live (s.redact a i)); have h₁:= P.coefficient_perm V' V e w (x:=crop X (s.live (s.redact a i))) (z:=X o); rw [show crop X (s.live (s.redact a i)) ∘ e = _ from (wheel X (no_shadow s i a) (pruned H hy)), show V' ∘ e= _ from hwheel p z (no_shadow s i a) (pruned H hy)] at h₁; exact h₁
lemma red_conf (o:I)(w:Exterior C.book) (h:Injective (beside (OPE.away (crop X (s.live (s.redact a i))) (X o)) (bearing w))) : Injective (beside (OPE.away (beside (sole (X i)) (crop X (s.external a i))) (X o)) (bearing w)):=by
    let V:= red (no_shadow s i a) (pruned H hy); let E:= Equiv.sumCongr V (Equiv.refl (Fin w.n)); rw [← wheel X (no_shadow s i a) (pruned H hy)]; let y:= OPE.away (crop X (s.live (s.redact a i))) (X o); exact (show beside (OPE.away (crop X _ ∘ V) (X o)) (bearing w)=beside y (bearing w) ∘ E from funext fun i=>by cases i<;> rfl).symm ▸ h.comp E.injective -- U unused?
include hp
lemma offering (j:J): s.alter P a p x i d (fun j b v=> coalesce P (s.live b) (x j) v s.root w) j= coalesce P (s.live a) (x j) p s.root w - paidStep P w (crop p (s.live a)) q (OPE.away (crop (x j) (s.live a)) (x j i)) (x j s.root-x j i) d:=by
    let X:= x j; let y:= OPE.away (crop X (s.live a)) (X i); let V:= s.external a i; let q':= univ \ q; let Z:=crop p (s.live a); have he(j:I'):j∈ q' ↔ j.val∈s.external a i:= ⟨fun h=>mem_sdiff.mpr ⟨j.property,fun hx=>(mem_sdiff.mp h).2 ((hp j).2 hx)⟩,fun h=> mem_sdiff.mpr ⟨mem_univ _,fun hx=> (mem_sdiff.mp h).2 ((hp j).1 hx)⟩⟩
    unfold alter paidStep; refine congr_arg _ (sum_congr rfl fun w' hw'=>?_); let r:= P.letter w'; refine congrArg₂ (·*·) ?_ ?_
    · let e : (↑q:Type) ≃ A' := roll (b:=s.inputs a i) (filter_subset ..) hp; let s':= s.inputs a i; let u:= crop X s'; let z:=crop p s'
      rw [show chunk q y= OPE.away u (X i) ∘ e from rfl,show chunk q Z= z ∘ e from rfl, P.coefficient_perm z U.room.kernel.laws.toSymmetric e]; change P.ope w' u z (X i)=_; exact (by simpa only [sub_self] using (ope_away P z u (X i) (X i) w').symm) -- rw y Abbrev issue
    · let e:= roll (b:=s.external a i) (sdiff_subset : s.external a i⊆ s.live a) he; let z:= crop X V; let p':= crop p V; let E:= Equiv.sumCongr (Equiv.refl Unit) e; let z':= beside (sole (X i)) z; let B':= beside (sole r) p'
      have hZ: substituted q y= OPE.away z' (X i) ∘ E:= by funext u; rcases u with u|u; exacts [(sub_self ..).symm, rfl]
      change coalesce P _ X _ _ _ = P.ope _ (substituted q y) _ _; rw [hZ,show beside (sole r) (chunk (univ\q) Z)= B' ∘ E from (funext (fun u=>by cases u <;> rfl)),P.coefficient_perm B' U.room.kernel.laws.toSymmetric E]; rw [show P.ope w (OPE.away z' (X i)) B' (x j s.root -x j i) = _ from ope_away P B' z' (X s.root) (X i) w]; exact (redact_token U P X p w H hy r s.root).symm
omit hp

lemma unit_repair (h:s.Coterie f t M δ x R) (he:s.inputs a i=∅) (hP:P.Coherent): ∀ᶠ j in f, s.alter P a p x i d (fun j b v=> coalesce P (s.live b) (x j) v s.root w) j=0:=by
    let V:= U.room.kernel.laws.toSymmetric; let V':= U.phase.transport.injection; let c:=s.external a i; have hc:c=s.live a:=by unfold c external; rw [he,sdiff_empty]
    letI : IsEmpty A':= ⟨fun u=> notMem_empty u.val (he ▸ u.property)⟩
    filter_upwards [(eventually_all_finset (P.sheet w).support).mpr (fun u hu=> (h.pinned u s.root (s.live (s.redact a i)) (h.eternity (redacted H hy) (Subset.refl ..))).mono (fun j hj=> red_conf U (x j) H hy s.root u hj))] with j hj; let X:=x j; let x':=crop X c; let p':= crop p c; let q:= P.test; let r v := P.ope w (beside (sole (X i)) x') (beside (sole v) p') (X s.root); let z:= X i
    have hf(w':Mode U.sector.derivatives): coalesce P (s.inputs a i) X p i w'= P.test w' d (S.project d (C.book.scalar d)):=by rw [coalesce,empty_coeff P _ _ _ U.room.kernel, ← P.affinity V V' _ (S.unit 0) (Nat.zero_le d), U.sector.derivatives.fixs V' U.room.kernel.laws (Nat.zero_le d)]; rfl
    have ht(w':Mode U.sector.derivatives): coalesce P (s.live (s.redact a i)) X (update p i (P.letter w')) s.root w= r (P.letter w'):= (redact_token U P X p w H hy _ _).symm
    unfold alter; apply sub_eq_zero.mpr; change coalesce P (s.live a) X p s.root w= ∑ j ∈ bands U.sector.derivatives _, _; change coalesce P (s.live a) X p s.root w = ∑ j∈ bands U.sector.derivatives d,coalesce P (s.inputs a i) X p i j*coalesce P (s.live (s.redact a i)) X (update p i (P.letter j)) s.root w; simp_rw [hf,ht]; refine Eq.trans (b:= r (C.book.one d)) ?_ (P.phaseAtRows V V' hP w _ _ _ _ _)
    conv_lhs=> arg 2; rw [← hc] -- coalesce arg2
    exact (unit_words P U.room.kernel p' w d hj).symm
end YM.OPE.Arboreal.Mountain

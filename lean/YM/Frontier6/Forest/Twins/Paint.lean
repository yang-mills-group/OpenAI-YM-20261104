import YM.Frontier6.Forest.Twins.Split

/-! Uniformly eventually in finite tags, projection questions. The estimated
 flatness is relative to every power loss on a clock; don't confuse with
 flatness through formal grades of a prescribed coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book} {T: Fareway I}{b a c z:ℝ}{P Q:Fabric I}{K:Final C H S}{A B:Art S I}{A' B':ℕ→ Art S I}
variable [Fintype V][DecidableEq V]{v:V→ S.Tag}
set_option quotPrecheck false
local notation "ℚ"=> Query T P K v
namespace Query
variable (h:Query T P K v A b a)
include h
lemma exceeds (hb:b≤c): Query T P K v A c a:=fun y hy he s=> (h y hy he s).too hb
lemma cf (he:Agrees T K A B): Query T P K v B b a:=fun y hy hP s=> (h y hy hP s).cf (he.mono fun i hi=>hi (assembly S (y i) v) (s i))
lemma add (hp:Query T P K v B b a): Query T P K v (A+B) b a:=by
   intro y hy hr s; rw [add_mul]; exact ((h y hy hr s).add (hp y hy hr s)).cf (Eventually.of_forall fun i=>(map_add (poll S _) _ _).symm)
lemma sub (hp:Query T P K v B b a): Query T P K v (A-B) b a:=by intro y hy hr s; rw [sub_mul]; exact ((h y hy hr s).sub (hp y hy hr s)).cf (Eventually.of_forall fun i=>(map_sub (poll S _) _ _).symm)
lemma scale {c:I→ℂ}(he:T.Costs c z): Query T P K v (fun i=> c i • A i) (z+b) a:=by
   intro y hy hr s; refine ((he.mul (h y hy hr s))).cf ?_; filter_upwards with i; unfold polled; rw [Pi.mul_apply,Pi.mul_apply,smul_mul_assoc,map_smul];rfl
omit h
lemma zero : Query T P K v 0 b a:=by intro y hy hh s; rw [zero_mul]; exact Costs.free.cf (Eventually.of_forall fun _=> (map_zero ..).symm)
end Query
lemma agreement_sub {Y Z: Art S I} (h:Agrees T K A B)(he:Agrees T K Y Z): Agrees T K (A-Y) (B-Z):= by filter_upwards [h,he] with i hi he; change Tale.Congr K (A i-Y i) (B i-Z i); rw [sub_eq_add_neg,sub_eq_add_neg,← neg_one_smul ℂ (Y i),← neg_one_smul ℂ (Z i)]; exact hi.add K (he.smul K _)
variable (v) (hC:Ribbon C H S)
namespace Prism
include hC
lemma rent (h:Prism K T b P A A')(he:0<b)(ha:a<b): ∃ u:ℝ, Query T P K v A u a:= by
   induction h with
   | battery h hk hv=> exact ⟨_,Flare.base_cost K hC h hv he.le hk v ha.le⟩
   | add _ _ ih jh=> obtain ⟨w,hw⟩:=ih; obtain ⟨p,hp⟩:=jh; exact ⟨max w p, (hw.exceeds (le_max_left ..)).add (hp.exceeds (le_max_right ..))⟩
   | scale h hv ih=> obtain ⟨p,hp⟩:=ih; obtain ⟨w,hw⟩:= h.color; exact ⟨_,hp.scale hw⟩
   | congruence h hv hx ih=> obtain ⟨p,hp⟩:=ih; exact ⟨p,hp.cf hv⟩
   | zero=> exact ⟨0,Query.zero⟩
lemma improving (h:Prism K T b P A A')(he:0<b)(ha:a<b)(u:ℝ) : ∀ᶠ d:ℕ in atTop, Query T P K v (A-A' d) u a:= by
   induction h generalizing u with
   | battery h hk hv=> exact Flare.fleets K hC u v he h hv hk ha
   | @add X Y X' Y' h g ih jh=>
      filter_upwards [ih u,jh u] with d i j; exact (i.add j).cf (Agrees.cf (Filter.EventuallyEq.of_eq (show X-X' d + (Y-Y' d)= _ from (by rw [Pi.add_apply]; abel))))
   | congruence h hv hx ih=> filter_upwards [ih u,hx] with i hi h; exact hi.cf (agreement_sub hv h)
   | zero=> simp only [Pi.zero_apply,sub_self]; exact Eventually.of_forall fun _=> Query.zero
   | @scale X X' Z Z' h hv ih =>
      obtain ⟨p,hp⟩:= h.color; obtain ⟨n,hn⟩:= hv.rent v hC he ha; filter_upwards [h.change (u-n), h.change p, ih (u-p)] with d hf hh hk
      have hm:T.Costs (Z' d) p:= (hp.sub hh).cf (Eventually.of_forall fun i=>by simp)
      let f:= fun i=> (Z-Z' d) i • X i; let g:= fun i=> Z' d i • (X-X' d) i
      have hr:Query T P K v (f+g) u a:= Query.add ((hn.scale hf).exceeds (sub_add_cancel ..).le) ((hk.scale hm).exceeds (Eq.le (by ring)))
      apply hr.cf; refine Agrees.cf (Eventually.of_forall fun i=>?_); unfold f g; simp_rw [Pi.add_apply,Pi.sub_apply,sub_smul,smul_sub]; abel
lemma gains (h:Prism K T b P A A')(he:0<b)(u:ℝ) : ∀ᶠ d:ℕ in atTop,∀ s:I→StateIndex K,T.Costs (polled K s (A-A' d)) u:= by
    let v := fun i:Empty=> (Empty.elim i:S.Tag); let x:I→ Empty→ E4:= fun i j=>0; have hx:inscription S x v=1:=by ext1 i; unfold inscription assembly; simp
    refine (h.improving v hC he he u).mono fun d hd s=>?_ ; specialize hd x (fun a b _ => Empty.elim a) ?_ s -- unfold query manually?
    swap
    · simpa only [hx,mul_one] using hd
    intro b hb; exact Eventually.of_forall fun i y hy z ⟨_,_⟩=> by contradiction
-- fixed $D$ projection errors from moving horizons. Flat order prior to sampling across all finite basis lists and s.
lemma shineout (h:Prism K T b P A A')(he:0<b){x:I→ E4}{d:ℕ}(hc:Forest.Centered T P x K d)(hv:Intact T P A)(hh:∀ᶠ i in atTop, Intact T P (A' i)): Flat T (fun i j=> pitch K (x j) d (A j)-pitch K (x j) d (A' i j)):=by
    intro u
    filter_upwards [eventually_all.mpr fun z:Fin (d+1)=> eventually_all.mpr fun p:(hand K z.val).list=> eventually_all.mpr fun q:Bool=> eventually_all.mpr fun y:roles S (floated (p.val.flip K q))=> h.improving (line (floated (p.val.flip K q)) y) hC he he u,hh] with i hi h'
    have hL:= lights K d hc hv; have hR := lights K d hc h'; have hv: ∀ᶠ j in T.via,Visible K (x j) d ((A-A' i) j):= (hL.and hR).mono fun _ hi=> hi.1.sub K hi.2
    refine ((moonlit K hc hv hi).mapped (weight K d)).cf ?_; exact (hL.and hR).mono fun j hj=> pitch_sub K _ _ _ hj.1 hj.2
end Prism
end YM.Frontier6.Forest

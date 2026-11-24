import YM.Frontier6.Forest.Render.Aperture

/-! Array of deepest-band groups. Explicit comparison price to carry to
 ground readings. This supersedes uniform-turnover for shape-reordering
 programming purposes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest.Flare
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}{T:Fareway I}{b a c p q t:ℝ}
variable [Fintype V][DecidableEq V]
variable (K:Final C H S)(h:Road.Ribbon C H S)
attribute [local instance] Spark.ft Spark.de Spark.ne
lemma safe_joint {F:V→ Spark S I}{P:Fabric I}(h':∀ v:V,(F v).Shine T b P) (he:Wide T (home F) a)(hb:a<b): Wide T (whole F) b:=by
    rintro ⟨i,r⟩ ⟨j,s⟩ hh; by_cases hk:i=j
    · subst j; exact (h' i).level (fun hz=> hh (congr_arg (Sigma.mk _) hz))
    let x(k:I):= (F i).whereAt k r; let y(k:I):= (F j).whereAt k s; let z:=(F i).origin; let w:=(F j).origin
    have hv:= ((ReachWide.motion (x:=z) (y:=w) (he hk) ((h' i).lights r) hb).flip.motion ((h' j).lights s) hb).flip.mono hb.le
    change ReachWide T x y b; simpa only [z,w,sub_add_cancel] using hv
-- root uniform expense
include h
lemma quiescent {F:V→ Spark S I}{P:Fabric I}(h':∀ v:V,(F v).Shine T b P) (he:Wide T (home F) a) (ha:0≤b)(hb:a<b): Query T P K (fun i:Empty=> Empty.elim i) (showAt F) (wages (words F)*b) b:=by
    rw [showAt_raw]; intro y hy hf s
    -- simpler crude
    rw [show inscription S y _=(1:Art S I) from funext fun i=>by unfold inscription assembly; rw [Finset.univ_eq_empty,Finset.prod_empty]; rfl, mul_one]; exact crude K h.grill (safe_joint h' he hb) ha _ _
-- more useful variant arbitrary exterior
lemma base_cost [Fintype X][DecidableEq X]{F:V→ Spark S I}{P:Fabric I}(h':∀ v:V,(F v).Shine T b P) (he:Wide T (home F) a) (ha:0≤b)(hb:a<b)(v:X→ S.Tag){c:ℝ}(hc:c≤b): Query T P K v (showAt F) (wages (Sum.elim (words F) v)*b) c:=by
    rw [showAt_raw]; intro y hy hf s
    have hx:= unity (safe_joint h' he hb) (hy.higher hc) (x:=whole F) (fun i j=> (hf.wide ((h' i.fst).supports.contains (contains_sheet _ i.snd)) (contains_sheet y j)).mono hc) -- supply contains
    · refine (crude K h.grill hx ha _ s).cf (Eventually.of_forall fun i=>?_); exact congr_arg (poll S _) (concatenates S (whole F i) (words F) (y i) v)
    -- membership hole
-- explicit prices
def levy (F:V→ Spark S I)(p q:ℝ):ℝ:= ∑ i:V,(forestPower (grades (F i).tags) q 2 1 + p)
lemma cost_wall {F:V→ Spark S I}{P:Fabric I}(h':∀ v:V,(F v).Shine T b P) (he:Wide T (home F) (b*t)) (hc:0<b)(hT:t<a) (ha:0<a)(hp:a<p)(hq:p<q)(hZ:q<1)(d:ℕ)(s:I→StateIndex K): T.Costs (polled K s (showAt F-shared K F d)) (b*(levy F p q-d*(q-p)^2)):=by
    let H:=T.surge hc; have hh(i:V): Aspect H (fun k=> Fork.cutTo i (offset F k)):=by
        apply Wide.ties _ ((h' i).lights) hc
        intro j k hk b hb;
        filter_upwards [(h' i).level hk b hb] with w hw; rw [sub_sub_sub_cancel_right]; exact hw
    apply (surges _ hc).2
    obtain ⟨j,hj⟩:= picks C.S C.path.levels.fits.mesh H 2 two_pos; obtain ⟨l,hl⟩:=picks C.S C.path.levels.fits.mesh H a ha; obtain ⟨k,hk⟩:=picks C.S C.path.levels.fits.mesh H p (ha.trans hp); obtain ⟨m,hm⟩:=picks C.S C.path.levels.fits.mesh H q ((ha.trans hp).trans hq)
    exact (Fork.timeband K h (words F) d hh (he.surging hc) hT hp hq hZ s hj hl hk hm one_lt_two (ha.trans hp) zero_lt_one).cf (Eventually.of_forall (fun i=>comparing K F d i (s i)))
end YM.Frontier6.Forest.Flare

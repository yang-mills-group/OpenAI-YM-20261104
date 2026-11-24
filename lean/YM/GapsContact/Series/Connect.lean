import YM.GapsContact.Series.Gateway
/-!
# Exact relativistic extension contract from all-order Euclidean inputs

Use within the *aligned* common frames and phase vocabulary (we provide them up to cap4
through the specified exact order in the stress scheme, and require genuinely same objects if
using any extension of those results). Uses ambient points: consecutive-relative (or Sidecar
`Index`) tests are also permitted, but no changes to Euclidean area. Asymptotic series claims
will be conditional only on `Pattern.Fan` profiles and Banks of the predictions. No assumption
of real-time analytic inputs, adaptation or comparison to Wilson coefficients on any complex
region. Need Actual RG continuation beyond current hypotheses to supply all-order matching itself.
No implicit use of the UV_INDEX construction (different schedules/histories) for that comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Craft
open Function Filter Set MeasureTheory Metric Boundary Analysis Tunnel Jost Ascent EveryPhase
open Pattern Work.C20 Spec Next.BOUNDARY Trace Trace.Pilot Trace.Terrace
open scoped Topology BigOperators ContDiff InnerProductSpace Classical
universe u
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S} (L:Almanac F)
variable {n:ℕ}{D:∀ _:Survey F,∀ n, Blanket n}
variable (X:∀ i:Survey F, (Survey.reads L i).world.Aurora (D i))
variable {hG:G.Simple} (Z:Roll.{u} F hG L) {g:ℝ→ℝ}(hg:Coupling G g)
variable {d:Fin n→ℕ}(v:∀ i:Fin n,ℝ→ S.Field (d i)) (hv:∀ i,Measured F (d i) (v i))
local notation "ℵ" => focus F
local notation "M"=> wickSlice n

variable (U:ℕ→Points n→ℂ) (hp: Fan (focus F) (metric F g) (eu S F v) U (ordered n))

-- use U formal coefficient-wise (complex functions only by pullback to adapted real section),
-- any extensions outside that real section drop out of primary hypothesis
lemma rect_injective (n:ℕ): Injective (wickSlice n):=by
   intro x y h; ext i a
   have he:(wickSlice n x) (i,a)=(wickSlice n y) (i,a):=by rw [h]
   by_cases hc: a=timeAxis <;> simpa [wick_apply,hc] using he

def anchors (U:ℕ→Points n→ℂ)(i:ℕ)(z:Full n):= U i (invFun (wickSlice n) z)
lemma at_root (i:ℕ)(x:Points n):anchors U i (M x)=U i x:=congr_arg _ (leftInverse_invFun (rect_injective _) _)
lemma chart_seed {T:Set (Full n)} (hT:IsOpen T)(hs:IsPreconnected T)(hh:tube n⊆T):∃ K:Set (Points n),IsCompact K ∧ K⊆ordered n ∧ Charter (wickSlice n '' K) T:=by
   let x:= Boundary.place 0 (rate n); have hx:x∈ordered n:=by change readings x∈east n; unfold x; rw [readings_place]; intro i j h; unfold rate; exact_mod_cast h
   obtain ⟨r,hr,hR⟩:=Metric.mem_nhds_iff.mp ((ordered_open n).mem_nhds hx)
   let K:=closedBall x (r/2); have hk:K⊆ordered n:= (closedBall_subset_ball (half_lt_self hr)).trans hR
   obtain ⟨b,hb,hB⟩:=Metric.mem_nhds_iff.mp (hT.mem_nhds (hh (wick_tube hx)))
   obtain ⟨e,he,hu,h⟩:= splash (M) (merges M (wick_span n)) x (half_pos hb) (half_pos hr)
   have hv:closedBall (M x) (b/2)⊆ T:= (closedBall_subset_ball (half_lt_self hb)).trans hB
   exact ⟨K,isCompact_closedBall ..,hk, hT,hs,image_subset_iff.mpr (fun x hx=> hh (wick_tube (hk hx))),M x,e,_,isCompact_closedBall ..,hv,he,(closedBall_subset_closedBall hu.le).trans hv,h⟩ -- constructor packaging?

include Z hg hv hp in
lemma root_power (K:Set (Points n))(hk:IsCompact K)(hK:K⊆ordered n) : Expansion (focus F) (metric F g) (ship L X v) (anchors U) (wickSlice n '' K):=by
   obtain ⟨m⟩:= train (hG:=hG) F hg; have he:= hp.power m (ordered_open _) (real_breeze hg L X v hv Z) hk hK
   intro q; apply tract (wickSlice n) -- m explicit
   · -- projected to M
     apply (he q).congr; filter_upwards [smiling F] with i hi x hx; change eu S F v i x-Pattern.chart U _ q x= _-Pattern.chart (anchors U) _ q (M x)
     rw [truth L X v i hi (hK hx)]; simp only [Pattern.chart,at_root]

omit hv Z hp hg in
lemma exchange_expansion {Ω E:Type*}{f:Filter Ω}{g:Ω→ℝ}{F G:Ω→ E→ℂ}{U:ℕ→E→ℂ}{S:Set E}(H:Expansion f g F U S)(hg:∀ᶠ i in f,EqOn (F i) (G i) S): Expansion f g G U S:=
   fun q=> (H q).congr (hg.mono fun i ht x hx=> by unfold Rem;rw [ht hx])

-- ambient glue to ANY Jost zone, with equality inside its whole tube portion
-- giving analytic cost at every compact (standard common scheme). Charts all use the same X.
variable (P: Scheme n)(B:∀ j:Fin n, Blade F (d j) P.e)

def transit (P: Scheme n) := tube n ∪ P.zone
def extra (i:Index F):= panel L i.2 (X i.2) P B (fun j=>v j i.1) i.1
def cargo(i:Index F)(x:Full n):= if x∈ tube n then ship L X v i x else extra L X v P B i x
lemma first (i:Index F):EqOn (cargo L X v P B i) (ship L X v i) (tube n):=by intro x hx; rw [cargo, if_pos hx]
lemma latter (i:Index F)(hi:0 < i.1): EqOn (cargo L X v P B i) (extra L X v P B i) P.zone:= by
    intro x hx; unfold cargo; split; next he=> exact (panel_reached L i.2 _ P B _ hi (Set.mem_inter hx he)).symm
    rfl
lemma transit_open : IsOpen (transit P):= (south n).union P.clear
lemma transit_pre : IsPreconnected (transit P):=by obtain ⟨x,hx,hK⟩:=P.starts; exact IsPreconnected.union x hK hx (convex_tube n).isPreconnected P.arch.isPreconnected -- signature
lemma extra_eq (i:Index F) (x:Full n): extra L X v P B i x=ship L X (fun j r=> fly F (d j) P (B j) (v j r)) i (reach P.g P.e P.speed x):=rfl

lemma bridge_hol : ∀ᶠ i in focus F, AnalyticOnNhd ℂ (cargo L X v P B i) (transit P):=by
   filter_upwards [ship_motion L X v,smiling F] with i hi h x hx
   rcases hx with hx|hx
   · apply (hi x hx).congr
     filter_upwards [(south n).mem_nhds hx] with y hy using (first L X v P B i hy).symm
   apply (panel_analytic L i.2 _ P B _ h x hx).congr
   filter_upwards [P.clear.mem_nhds hx] with y hy using (latter L X v P B i h hy).symm

include Z hg hv
lemma transit_estimate : ∃ b:ℕ,Scoped (focus F) (cargo L X v P B) (transit P) (fun i=>(metric F g i)⁻¹^b):=by
   let v' := fun j r=> fly F (d j) P (B j) (v j r); let X':= extra L X v P B; let Q:Full n→L[ℂ] Full n:=reach P.g P.e P.speed
   obtain ⟨c,hc⟩:= ship_expense hg L X v hv Z
   obtain ⟨b,hb⟩:= ship_expense hg L X v' (fun i=> fly_measured Z P (B i) (hv i)) Z
   let Y:=fun i:Index F => (metric F g i)⁻¹; have he : ∀ᶠ i in focus F,1 ≤ Y i:=by obtain ⟨m⟩:=train (hG:=hG) F hg; exact m.short.mono (fun _ h=> (one_le_inv₀ h.1).mpr h.2)
   refine ⟨b+c,fun K hk hs=>?_⟩; apply TagPrice.patch hk (he.mono fun _ h=> pow_nonneg (zero_le_one.trans h) _); intro x hx
   rcases hs hx with hx|hx
   · obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp ((south n).mem_nhds hx); let K:= closedBall x (r/2); have hK: K⊆ tube n:=(closedBall_subset_ball (half_lt_self hr)).trans hR
     refine ⟨ball x (r/2),isOpen_ball,mem_ball_self (half_pos hr), (?_ : TagPrice (focus F) (cargo L X v P B) K _).parent ball_subset_closedBall⟩
     apply ((hc K (isCompact_closedBall ..) hK).up (he.mono fun i hx=> pow_le_pow_right₀ hx (show c ≤ b+c from Nat.le_add_left ..))).congr; exact Eventually.of_forall fun i x hx=> (first L X v P B i (hK hx)).symm
   obtain ⟨r,hr,hR⟩:=Metric.mem_nhds_iff.mp (P.clear.mem_nhds hx); let K:=closedBall x (r/2); have hK:K⊆P.zone:= (closedBall_subset_ball (half_lt_self hr)).trans hR
   refine ⟨ball x (r/2),isOpen_ball,mem_ball_self (half_pos hr), (?_ : TagPrice (focus F) (cargo L X v P B) K _).parent ball_subset_closedBall⟩; obtain ⟨A,hA,h⟩:=hb (Q '' K) ((isCompact_closedBall ..).image Q.continuous) (image_subset_iff.mpr (fun x hx=> P.fits (hK hx)))
   refine ⟨A,hA,?_⟩; filter_upwards [h, he,smiling F] with i h ht hx p hp
   rw [latter L X v P B i hx (hK hp),extra_eq]; exact (h _ (mem_image_of_mem Q hp)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (Nat.le_add_right ..)) hA)

structure Alliance (F:Final C f S) (L:Almanac F){d:Fin n→ℕ}{D:∀ _:Survey F,∀ n, Blanket n}(X:∀ i:Survey F, (Survey.reads L i).world.Aurora (D i))(g:ℝ→ℝ)(v:∀ i:Fin n,ℝ→ S.Field (d i))(U:ℕ→Points n→ℂ)(J:ℕ→Full n→ℂ) : Prop where
   residence : Pattern.Extension (focus F) (ship L X v) (metric F g) J (tube n)
   route : ∀ (i:ℕ)(x:Points n), x∈ordered n→ J i (wickSlice n x)=U i x
   gate (P:Scheme n)(B:∀ j:Fin n,Blade F (d j) P.e): ∃ H:ℕ→Full n→ℂ, (∀ j,EqOn (H j) (J j) (tube n)) ∧ Pattern.Extension (focus F) (cargo L X v P B) (metric F g) H (transit P)

include hp in
lemma propagate : ∃ J:ℕ→Full n→ℂ, Alliance F L X g v U J:=by
   obtain ⟨m⟩:=train (hG:=hG) F hg
   obtain ⟨K,hn,hK,hT⟩:=chart_seed (south n) (convex_tube n).isPreconnected (Set.Subset.refl _)
   have hy:= root_power L X Z hg v hv U hp K hn hK
   obtain ⟨b,h⟩:=ship_expense hg L X v hv Z
   obtain ⟨J,hj,hh⟩:=Pattern.stretch m hT ⟨ship_motion L X v,fun K hk hs=> ⟨b,h K hk hs⟩⟩ hy
   refine ⟨J,hh,fun i x hx=> ?_,fun P B=>?_⟩
   · have hf:= root_power L X Z hg v hv U hp {x} isCompact_singleton (singleton_subset_iff.mpr hx)
     rw [← at_root U]; exact Pattern.Extension.uniq m hh _ (wick_tube hx) (Set.image_singleton .. ▸ hf) _
   obtain ⟨b',hu⟩:= transit_estimate L X Z hg v hv P B
   have H : Charter (M '' K) (transit P):=by
      obtain ⟨x,d,K,hK,he,hd,hm,hV⟩:=hT.dock; refine ⟨transit_open P, transit_pre P, hT.pitch.trans subset_union_left, x,d,K,hK,he.trans subset_union_left, hd,hm.trans subset_union_left,hV⟩
   have hE:= Pattern.stretch m H ⟨bridge_hol L X v P B, fun K hk hx => ⟨b', hu K hk hx⟩⟩ (exchange_expansion hy (Eventually.of_forall fun i=> (first L X v P B i).symm.mono hT.pitch))
   obtain ⟨W,hW,hE⟩:= hE; exact ⟨W,fun i x hx=> Pattern.Extension.uniq m hE x (.inl hx) (exchange_expansion (hh.power _ isCompact_singleton (singleton_subset_iff.mpr hx)) (Eventually.of_forall fun i=> (first L X v P B i).symm.mono (singleton_subset_iff.mpr hx))) i,hE⟩

omit hv Z in
include hG in
-- Extensions on any scheme agree on overlaps through tube or edge. independent prescriptions not scaled-point choices.
lemma overlapped {W W':ℕ→Full n→ℂ}{Q:Scheme n}{B':∀ j:Fin n,Blade F (d j) Q.e} {z:Full n} (hh:z∈ P.zone∩Q.zone)(hs:shade z∈shores n)
   (H: Pattern.Extension (focus F) (cargo L X v P B) (metric F g) W (transit P))
   (H':Pattern.Extension (focus F) (cargo L X v Q B') (metric F g) W' (transit Q))(j:ℕ) : EqOn (W j) (W' j) (P.zone∩Q.zone):=by
   obtain ⟨m⟩:= train (hG:=hG) F hg; let K:=P.zone∩Q.zone; have hk:IsOpen K:= P.clear.inter Q.clear; obtain ⟨x,hx,hX⟩:= _root_.mem_closure_iff.mp (closure_tube z hs) K hk hh
   apply ((H.hol j).mono (inter_subset_left.trans subset_union_right)).eqOn_of_preconnected_of_eventuallyEq ((H'.hol j).mono (inter_subset_right.trans subset_union_right)) (P.arch.inter Q.arch).isPreconnected hx
   filter_upwards [(hk.inter (south n)).mem_nhds (mem_inter hx hX)] with p hp
   have he:p∈ tube n:=hp.2
   apply Pattern.Extension.uniq m H p (subset_union_left he) (?_:Expansion (focus F) (metric F g) (cargo L X v P B) W' {p}) j
   exact exchange_expansion (H'.power _ isCompact_singleton (singleton_subset_iff.mpr (subset_union_left he))) (Eventually.of_forall fun i=>((first L X v Q B' i).trans (first L X v P B i).symm).mono (singleton_subset_iff.mpr he))
end YM.GapsContact.Craft

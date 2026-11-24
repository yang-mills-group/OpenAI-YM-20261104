import YM.OPE.Coverage.Diagonal
import YM.OPE.Coverage.Fields

/-!
## Independent prices at many log-close physical shelves with the original cutoff provenance

The comparison tests give both weak Maxell measurements and more crude,
but now sub-*log-power*, unmixed moment upper bounds in the same bought frames,
ahead of positive-order matching. This still isn't a cumulative comparison
between those frames and one true fixed normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG
open Next.UVStress Spec Levy MeterTest Maxwell Next.Extract
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}{F:Order}{C:Family G}{S:Table C.book}{n:ℕ} (H:Final C F S)
set_option quotPrecheck false
local notation "mCb" => Bel C.book
private abbrev Γ(C:Family G) := Maxwell.Free.spin_free C.labels
structure Stored (r:ℕ→ℝ) (m n:ℕ)(μ:ℝ) extends Shelf H r m n μ where
   wheel : ℕ→Wheel C m
   receipt : Granular wheel F (Γ C) n μ
   stripe : Stripe wheel
   coup i:Fitted F (wheel i).toStation (maps i)
   spot i : (wheel i).r = path i

lemma Granular.comp' {n d:ℕ}{x:ℕ→Wheel C d}(r:ℕ→ℕ)(hr:Tendsto r atTop atTop) {μ A}(hx:Granular x F A n μ):Granular (x∘r) F A n μ:=by
   rcases hx with ⟨⟨ha,hb,hc,hd⟩,he,hf⟩
   refine ⟨⟨hr.eventually ha,hr.eventually hb,hr.eventually hc,hr.eventually hd⟩,he.comp hr,?_⟩
   intro k hk t ht w
   obtain ⟨a,b,c,e,f,g,h,i,j,l⟩:=hf k hk t ht w
   exact ⟨a∘r,b∘r,c∘r,e.comp hr,f.comp hr,hr.eventually g,hr.eventually h,i.comp hr,j.comp hr,hr.eventually l⟩

lemma sell_along {r:ℕ→ℝ}(h:Paved C F)(he:Fine r)(N D:ℕ)(μ:ℝ)(hμ:0<μ)(ht:Services C F S):Nonempty (Stored H r D (N+1) μ):=by
   let nn:=N+1
   obtain ⟨w,hw,hL,hW,hP⟩:= paid_on_demand h he (N+1) (Nat.le_add_left ..) D μ hμ (Maxwell.table_smooth C.labels) (Γ C)
   have hv:=Next.UVStress.supply_wheel w hW H.room.ordered H.room.kernel.smooth H.room.cutoff H.room.generic (Maxwell.table_smooth C.labels) hμ 1 one_pos
   obtain ⟨j,hj⟩:= eventually_atTop.mp hv;let q i:=max j i; let k:=w ∘ q
   have hq : Tendsto q atTop atTop := tendsto_atTop_mono (f:=id) (g:=q) (fun i=>le_max_right ..) tendsto_id
   choose y hb hc hd hf using fun i=> YM.OPE.Levy.harvested H.room.kernel H.room.ordered (Γ C) (k i).toStation (hj (q i) (le_max_left ..))
   obtain ⟨M,V,A,B,Ha⟩:=ht.along
   have hs : RoughFactory C:=by obtain ⟨a,b,c,h⟩:=ht.purchase; exact ⟨a,b,c,h.toTableTickets⟩
   refine ⟨⟨⟨fun i=>(k i).r,y,?_,?_,hb,fun i=>hc i,fun i hi=>approach H (q:=q) hq y hd hW hμ i hi, controlling H Ha hs ht.simpleGate hL hq y hd⟩,k,Granular.comp' _ hq hW,⟨fun p hp=>hq.eventually (hP.rate p hp)⟩,hd,fun i=>rfl⟩⟩
   · obtain ⟨hh,b,hb,hσ⟩:=hw
     refine ⟨fun i=>hh (q i), b,hb, ?_⟩
     filter_upwards [eventually_ge_atTop j, hσ] with i hi hσ
     change _ ≤ _
     simpa only [mark,k,q,max_eq_right hi,comp_apply] using hσ
   exact ⟨fun i=>(k i).rad, (Exists.choose_spec (Exists.choose_spec hL)).1.comp hq⟩

def fare(r:ℕ→ℝ)(i:ℕ):=Real.log (1+mark r i)
lemma fare_large(r:ℕ→ℝ)(hr:Fine r): Tendsto (fare r) atTop atTop:= Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ hr.2)
variable {r:ℕ→ℝ}{d m n:ℕ}{μ:ℝ}(p:Stored H r m n μ)
local notation "T₀" => fare p.path
local notation "W" => p.wheel
lemma Stored.price_stripe: RateLE atTop T₀ (fun i=> (W i).σ⁻¹) 0:=by
   intro q hq
   filter_upwards [p.fades.2.eventually_gt_atTop 0,p.stripe.rate q hq] with i hi hσ
   rw [Real.norm_of_nonneg (inv_nonneg.mpr (W i|>.stripe.le))]
   rw [show rents (p.wheel) i=mark p.path i from congrArg (fun t=> -Real.log t) (p.spot i)] at hσ
   unfold fare; rw [mul_comm]; convert hσ using 1
   symm; change _^q =_; exact Real.rpow_def_of_pos (by linarith only [hi]) _

local notation "πd" => (fun i=> (mCb).Field i)
set_option maxHeartbeats 6000000

-- Pass to exact tables with this limit labelling. This still prices the

lemma Window_spot {m0 k j:ℕ}{σ A : ℝ}(t:Caps j)(w:Ribbon (mCb) t)(hu:∀ a, t a ≤ m) (ha: Next.UVStress.bulk (C:=C) (t:=t) ((W d).tones hu w) F A k)(hσ:0 < σ)(hm: C.S.a m0 < σ)(hv:m0≤k)
   (hx:(j:ℝ)*(2*(3*C.S.a k)) < C.S.a m0) (z:Points j)(hz:z∈airy j σ):
      ‖disc (panels (p.maps d) ∘ hang t w) z‖ ≤ A^j :=by
   obtain ⟨u,hu0,hb,hW⟩:=p.coup d
   choose Y hY hT using fun i:(Fin j) =>hW ⟨t i,Nat.lt_succ_of_le (hu i)⟩ (w i)
   have he:= large_gate H.room.cutoff H.room.kernel.smooth H.room.generic u hb ((W d).tones hu w) Y (tendsto_pi_nhds.mpr hY) hσ m0 k hm hv hx ha z hz
   have hu': z∈conf j:= spaced_conf hσ (fun i l hi=> (hz i l hi).le)
   replace hu': disc ((panels (p.maps d)) ∘ hang t w) z = S.value t z Y:=by
      unfold disc
      rw [← show S.classTokens ∘ (ripped (t:=t) (C:=C) Y) = panels _ ∘ hang t w from ?grid, S.at_project S H.room.kernel.laws.toSymmetric (fun _=>le_rfl) hu']
      case grid=> exact funext fun i=> Sigma.ext rfl (heq_of_eq (hT i).symm)
      rfl
   rwa [hu']

lemma airy_spending {j:ℕ}(t:Caps j)(u:record C t)(ht:∀a,t a ≤ m)(hj:j≤n)(hμ:0 < μ)
   (z:ℕ→Points j)(hz:∀ᶠ i in atTop,z i∈airy j ((W i).r/(2*μ))): RateLE atTop T₀ (fun i=>disc (panels (p.maps i) ∘ hang t (depthWord t u)) (z i)) 0 :=by
   let c:= T₀
   obtain ⟨e,A,B,hk⟩:= p.receipt.proof_ j hj t ht u
   have hf : RateLE atTop c (fun i=>(A i)^j) 0:=by
      refine (Stored.price_stripe H p).of_norm_le ?_
      filter_upwards [hk.off.eventually (gt_mem_nhds zero_lt_one),hk.pos] with i hi hv
      rw [Real.norm_of_nonneg (pow_nonneg hv.1 _), inv_eq_one_div,le_div_iff₀ (W i|>.stripe)]; exact hi.le
   refine hf.of_norm_le ?_
   filter_upwards [hk.costs,hz] with i hi hz
   obtain ⟨l,k,h₁,h₂,h₃,h₄⟩:= hi.crude
   exact Window_spot H p t _ ht h₄ (div_pos (W i|>.rad) (by positivity)) h₁ h₂ h₃ _ hz

private def Leased {j:ℕ}(t:Caps j)(i:ℕ)(z:Points j) := (S.classMoment S t z).compLinearMap (fun a=>p.maps i (t a))
lemma leased_shows {j:ℕ}(t:Caps j)(v:Ribbon (mCb) t)(i:ℕ)(z:Points j):Leased H p t i z v=disc (panels (p.maps i) ∘ hang t v) z :=rfl
lemma airy_list {j:ℕ}(t:Caps j)(v:Ribbon (mCb) t)(ht:∀i,t i ≤ m)(hj:j≤n)(hμ:0 < μ) (z:ℕ→Points j)(hz:∀ᶠ i in atTop,z i∈airy j ((W i).r/(2*μ))): RateLE atTop T₀ (fun i=>disc (panels (p.maps i) ∘ hang t v) (z i)) 0 :=by
   let Q(a):= coords (fun i=> πd (t i)) a v -- remove (C:=C)
   have h:= RateLE.sum (S:=Finset.univ) (f:=fun a i=> Q a * Leased H p t i (z i) (depthWord t a)) (a:=0) (fare_large p.path p.fades) (fun a _=> ?term)
   refine h.congr ?eq
   case term =>
       simp_rw [leased_shows]
       have c:= RateLE.const (Q a) (fare_large p.path p.fades)
       simpa only [zero_add] using c.mul (airy_spending H p t a ht hj hμ z hz)
   filter_upwards with i
   exact ((basis_tuple _ _ (Leased H p t i (z i))).symm.trans (leased_shows H p t v i (z i)))
end YM.OPE.Coverage

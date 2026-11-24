import YM.OPE.Coverage.Lengths
import YM.OPE.Coverage.Theory

/-!
## Ordered-limit field measurements on dense length shelves

Any Fitted cutoff sublimit sees the same smear comparisons, so this does
not identify an independent field or a fresh hierarchy. Draw the maps at
*fixed* regulator-station data, then pass to the weak length limits. `upper`
is relative to the actual planes, still a subpower amplification (not the
fixed-basis polynomial bound). No comparison error order in the log gained
merely from this limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG Next.UVStress Spec Levy
open Bid Dash Next.Extract Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}{D n:ℕ}
set_option quotPrecheck false
local notation "mCb" => Bel C.book
local notation "Rays" => (standard C).RealSpin

lemma full_smears {X : YM.Next.UVStress.Station C D}{p:Panel S}{R ε : ℝ}
    (H:S.Hierarchy)(h:F.Ordered C S)(w:Fitted F X p)(a:(mCb).RealSpin)(hp:X.Admissible F a n R ε) :
      ∀ m ≤ n, ∀ v : Fin m → (mCb).Tag, (∀ i,(v i).1 ≤ D) → ∀ t : Test m, tsupport t ⊆ Scaling.window R m → ∀ M : ℝ, 0 < M → (∀ x, ‖t x‖ ≤ M) →
         ‖t.applyTo (Next.UVStress.tested X.r p v) - t.applyTo (disc v)‖ ≤ ε * Next.UVStress.Station.charge v * M:=by
    -- from Station.harvested compareer but without repeating the extraction.
    intro m hm v hv t ht y hy ht'
    obtain ⟨b,hb,hU,hY⟩ := w
    let l i:Fin (D+1):= ⟨(v i).1,Nat.lt_succ_of_le (hv i)⟩
    let r j i:=X.atCut j (l i) ((v i).2)
    choose z hz he using fun i=> hY (l i) ((v i).2)
    let g i:=(v i).1
    have hh : S.integralOn g z (dilate X.rad t)=t.applyTo (Next.UVStress.tested X.r p v) := by
       unfold Table.integralOn; rw [zoom_integral]
       apply t.apply_eq; intro x hx
       change S.value g _ z = S.useAt S _ (panels p ∘ v)
       let l : Fin m → C.book.Token := fun i => ⟨g i,z i⟩
       rw [show panels p ∘ v = S.classTokens ∘ l from funext (fun i => by unfold panels Function.comp; change Sigma.mk (g i) (p (g i) ((v i).2)) = Sigma.mk (g i) (S.project (g i) (z i)); rw [he i])]
       exact (S.at_project S H.laws.toSymmetric (fun _ => le_rfl) ((enlarged X.rad _).1 hx) l).symm
    have hz : Tendsto (fun k : ℕ×ℕ => X.paid v hv t k.1 k.2) b (𝓝 (t.applyTo (Next.UVStress.tested X.r p v))) := hh ▸ calibrated_smear h b hU _ (v:=r) (x:=z) hz
    refine le_of_forall_pos_le_add fun η hη => ?_
    exact le_of_tendsto ((hz.sub_const (t.applyTo (disc v))).norm)
       ((show ∀ᶠ i in F.fuse, ‖X.paid v hv t i.1 i.2 - t.applyTo (disc v)‖ ≤ ε * _ * y + η from
          hp.short hm v hv t ht y hy ht' η hη).filter_mono hU)

-- bound of reader at each horizon in the shelf. All same maps even if
-- different examples needed later when strengthening the finite request.
structure Upper (p:ℕ→Panel S)(r:ℕ→ℝ)(A:DiffPlan S)(D:ℕ):Prop where
  weight (d:Fin (D+1))(e:Fin (d.val+1))(x:(mCb).Field d)(φ:S.Field d→ₗ[ℂ] ℂ) :
      (∀ y∈plane (U:=A) e, φ y = 0) → RateLE atTop (mark r) (fun i=> φ (p i d x)) (-(e:ℝ))
structure Shelf (V:Final C F S) (r:ℕ→ℝ) (D N:ℕ)(A:ℝ) where
  path : ℕ→ℝ
  maps : ℕ→Panel S
  window : Close r path
  fades : Fine path
  realism : ∀ k d, d ≤ D→ StraightAt V.room.kernel.spin (Maxwell.Free.spin_free C.labels) (maps k) d
  fixed : ∀ k,maps k 0 ((mCb).unit 0) = S.unit 0
  smears : ∀ n ≤ N, ∀ v: Fin n → (mCb).Tag, (∀ i,(v i).1 ≤ D) → ∀ t:Test n, tsupport t ⊆ Scaling.window A n → Tendsto (fun k=>t.applyTo (Next.UVStress.tested (path k) (maps k) v)) atTop (𝓝 (t.applyTo (disc v)))
  price : Upper maps path V.sector.derivatives D

variable (V:Final C F S){A B E D' R}{m:ℕ}(hA:Base C F A B R S D') (a:RoughFactory C) (hG:G.Simple){p:ℕ→Wheel C m}(hp:Lodged F p)
variable {μ:ℝ}{q:ℕ→ℕ}(hq:Tendsto q atTop atTop) (U:ℕ→Panel S)(hU:∀i,Fitted F (p (q i)).toStation (U i)) (hv:Granular p F (Maxwell.Free.spin_free C.labels) n μ)(hμ:0<μ)
include V hv hμ hq hU
lemma approach (i:ℕ) (h:i ≤ n)(v:Fin i→(mCb).Tag)(he:∀ j,(v j).1 ≤ m)(t:Test i)(ht:tsupport t ⊆ Scaling.window μ i): Tendsto (fun j=> t.applyTo (Next.UVStress.tested (p (q j)).r (U j) v)) atTop (𝓝 (t.applyTo (disc v))):=by
    apply Metric.tendsto_nhds.mpr; intro ε hε
    obtain ⟨M,hM,hw⟩:= Next.UVStress.test_bounded t
    let c:=Next.UVStress.Station.charge v*M; have hc:0 ≤ c:=by unfold c Next.UVStress.Station.charge; positivity
    have hd:0 < ε/(1+c):=by positivity
    filter_upwards [hq.eventually (Next.UVStress.supply_wheel p hv V.room.ordered V.room.kernel.smooth V.room.cutoff V.room.generic (Maxwell.table_smooth C.labels) hμ _ hd)] with j hj
    -- Maxwell.free_smooth
    have he' : ε/(1+c) * Next.UVStress.Station.charge v * M < ε := by rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 1+c)]; dsimp only [c] at *; nlinarith only [hε]
    rw [dist_eq_norm]; exact ((full_smears V.room.kernel V.room.ordered (hU j) _ hj i h v he t ht _ hM hw).trans_lt he')
include a hp hA hG
omit hv hμ
lemma controlling : Upper U (fun i=>(p (q i)).r) V.sector.derivatives m:=by
    obtain ⟨X,z₀,z,H⟩:=a
    let T:= mark (fun i=>(p (q i)).r)
    have ht:Tendsto T atTop atTop:= (Exists.choose_spec (Exists.choose_spec hp)).1.comp hq
    constructor; intro d e x φ hz η hη
    let Γ:=η+e.val
    have he:0<Γ:=by dsimp only [Γ]; linarith only [hη]
    let g:=φ.toContinuousLinearMap
    let c:=‖g‖*‖x‖
    have hy(i) : Real.exp (Γ/2*T i)*Real.exp ((Γ/2-(e:ℝ))*T i)=Real.exp (η*T i):=by rw [←Real.exp_add]; unfold Γ; congr 1; ring
    filter_upwards [RateLE.const c ht (Γ/2) (by positivity),hq.eventually (impact H hA V.phase.transport.injection hG hp d e _ (half_pos he))] with i hi hv
    obtain ⟨b,hb,hq,hz'⟩:= hU i; obtain ⟨k,hk,hW⟩:=hz' d x; obtain ⟨y,hy',hcost⟩:=hv b hq x k hk
    rw [hW]
    calc _ = ‖φ (S.project _ k - y)‖ :=by rw [map_sub,hz _ hy',sub_zero]
         _ ≤ ‖g‖ * ‖S.project _ k - y‖ := g.le_opNorm _
         _ ≤ ‖g‖ * (Real.exp ((Γ/2 - ↑e)*T i)*‖x‖) := mul_le_mul_of_nonneg_left hcost (norm_nonneg g)
         _ = c*Real.exp ((Γ/2 - ↑e)*T i):= by unfold c; ring
         _ ≤ Real.exp (η*T i):= hy i ▸ mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs,abs_of_nonneg (by unfold c; positivity)] at hi; exact hi) (Real.exp_pos _).le

omit a hp hA hG hq hU
include hv hμ
local notation "H" => (Maxwell.Free.spin_free C.labels)
lemma for_one {r}(hr:Close r (fun i=>(p i).r)) (hq:Tendsto q atTop atTop)(he:∀ᶠ i in atTop,q i=i)(hp:Lodged F p)(hA:Base C F A B R S D') (a:RoughFactory C) (g:G.Simple) :Nonempty (Shelf V r m n μ):=by
    have hi: ∀ᶠ i in atTop, ((p (q i)).toStation.Admissible F H n μ 1) := hq.eventually (supply_wheel p hv V.room.ordered V.room.kernel.smooth V.room.cutoff V.room.generic (Maxwell.table_smooth C.labels) hμ 1 one_pos)
    obtain ⟨k,hk⟩:= eventually_atTop.mp hi
    let z(i:ℕ):=max k i
    have hq':Tendsto (q∘z) atTop atTop:= hq.comp (tendsto_atTop_mono (f:=id) (g:=z) (fun i=>le_max_right ..) tendsto_id)
    have hw : ∀ j, ((p (q (z j))).toStation.Admissible F H n μ 1):= fun j=>hk _ (le_max_left ..)
    choose U hB hC hD hE using fun j=> Levy.harvested V.room.kernel V.room.ordered H (p (q (z j))).toStation (hw j)
    let y i:=(p (q (z i))).r
    have hh : Fine y:=⟨fun i=>(p _).rad, (Exists.choose_spec (Exists.choose_spec hp)).1.comp hq'⟩
    have he' : y=ᶠ[atTop] fun i=>(p i).r:=by
         filter_upwards [he,eventually_ge_atTop k] with i hi h; change (p (q (z _))).r=_; rw [show z i=i from max_eq_right h,hi]
    obtain ⟨h1,c,h2,h3⟩:=hr
    refine ⟨⟨y,U,⟨hh.1,c,h2,?_⟩,hh,hB,hC,fun i h=> approach V (q:=q∘z) hq' U hD hv hμ i h,controlling V hA a ?_ hp hq' U hD⟩⟩
    · filter_upwards [he',h3] with j hj hh; unfold mark at *; rwa [hj]
    exact g 

omit hv hμ
include hG
lemma populated {r:ℕ→ℝ}(he:Fine r)(N D:ℕ)(μ:ℝ)(hμ:0<μ)(h:Paved C F)(ha:RoughFactory C)(hA:Base C F A B R S D'): Nonempty (Shelf V r D (N+1) μ):=by
   obtain ⟨w,hw,hL,hW,_⟩:= paid_on_demand h he (N+1) (Nat.le_add_left ..) D μ hμ (Maxwell.table_smooth C.labels) H
   exact for_one V hW hμ hw (q:=id) tendsto_id (Eventually.of_forall fun i=>rfl) hL hA ha hG
end YM.OPE.Coverage

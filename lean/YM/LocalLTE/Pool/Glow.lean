import YM.LocalLTE.Pool.Port
import YM.LocalLTE.Crafts.Trestle
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
local notation "W" => (bank n G M)
local notation "P" => iceCap (n:=n) G M p c x κ
variable (hs : Reliable G κ k) (hG:G.Simple)(hn:20<n.val) (hb:Decent c p)
-- Use βhat = t. Set χ models rates unit. 
variable (η:ℝ) (L:Side)
variable (ht : 1 ≤ t) (hx: ‖x‖≤2*t) (hd:c.direct≤1)(hG:G.Simple)(hn:20<n.val)(hP: p.threshold ≤ Start.threshold G p.order p.power) (ha:4 ≤ p.B)
-- rates extra. choose Λ_j. pay Price tψ small.History. Psi before Tor.
variable (he:η>0) (hh: 2*t*Start.item G p≤ η*t^(chip 0))(hv:∀ j:ℕ, j≤M → 2*t*(turnFee p*(betaF G t L)^(Urns.dust j-1))≤ η*t^(chip (j+1)))
variable (hW:∀ j:ℕ,j≤M→∀ (o:PlaqAxes), p.supBounds (0:Site n) (neighbors 4 0) (residual G (0,o)-glaze G o κ j) ((betaF G t L)^(Urns.dust j-1)))
local notation "P₀"=> Start.weight c x
variable {e γ γ' α β : ℝ}
open RG.Shoot Samples
local notation "T"=> Set.Icc (t/2) (2*t)
lemma coatE (i:ℕ)(x t:ℝ)(ht:t ≠ 0) : (iceCap (n:=n) G M p c x κ).regular i=(x/t) • (iceCap G M p c t κ).regular i:=by
    rw [reggo,reggo]; split
    · unfold part; rw [smul_smul]; congr 1; unfold Start.weight; field_simp
    rw [smul_zero]
lemma coatL (i:ℕ)(x t:ℝ)(ht:t ≠ 0) : (iceCap (n:=n) G M p c x κ).logarithm i=(x/t) • (iceCap G M p c t κ).logarithm i:=by
    dsimp only [iceCap]; split; next h=> rw [smul_smul]; congr 1; unfold Start.weight; field_simp
    rw [smul_zero]
set_option quotPrecheck false
local notation "V" x=> iceCap (n:=n) G M p c x κ
variable (hD:∀ x∈Set.Icc (t/2) (2*t), Ingredients (bank n G M) (iceCap G M p c x κ) p e γ) (hl:Loan p (t/2) α β γ')
include hD hl hb ht
lemma prelude : PreBound p (fun x=>V x) (W) T:=by
    have ht':0 < t:= zero_lt_one.trans_le ht; have he:t∈T:= ⟨(half_lt_self ht').le,by linarith⟩
    obtain ⟨_,_,_,H,_⟩:= (hD _ he).pays; obtain ⟨u,h,hF⟩:= H.pays
    obtain ⟨r,hq,hR⟩:= H.stamp.boundE
    have hz:Summable r:= by
       have hx:Quotes.anchored p ((W).reg) r e:= hR; exact (Price.influx hx|>.2.1).of_nonneg_of_le (fun i=>(hq i).1) (fun i=>p.loMass _ _ (hq i).1)
    let v (i:ℕ):=Start.cash n p α i
    have hw :Summable v:= (Padded.has (α:=Start.Foot n) (g:=Start.offer p α) (f:=v) (fun i=>rfl)).summable
    let V':=Real.exp (-β) • v; have hv:Summable V':= hw.mul_left _ -- edit
    have hU x (hx:x∈T): ‖x/t‖≤2:=by
       have h:0≤x:= ((half_pos ht').le).trans hx.1; rw [Real.norm_of_nonneg (div_nonneg h ht'.le)]; exact (div_le_iff₀ ht').mpr hx.2
    refine Payments.pre_finite («T»:=T) (d:=fun x=> iceCap G M p c x κ) (p:=V') (q:=fun i=>2*u i) ⟨_,he⟩ hv (h.mul_left _) (fun x hx i U=>⟨(show ‖(iceCap G M p c x κ).forced i U‖≤Real.exp (-β)*Start.cash n p α i from Start.forced_money hb hl.forced hl.slope hl.allows hx.1 i U), ?_⟩) ⟨fun i=>2*r i,hz.mul_left _, fun x hx i=> ?_⟩
    · rw [coatL (t:=t) _ _ _ _ _ _ ht'.ne',Pi.smul_apply,norm_smul]; exact mul_le_mul (hU _ hx) (hF i U) (norm_nonneg _) zero_le_two
    rw [coatE (t:=t) _ _ _ _ _ _ ht'.ne']; exact VerifiedReset.sup_le (Start.times_bound (x/t) (hq i)) (mul_le_mul_of_nonneg_right (hU _ hx) (hq i|>.1))
omit hl
lemma wick : Flow p (fun x=> V x) (W) T:=by
    have ht':0 < t:= zero_lt_one.trans_le ht; have he:t∈T:= ⟨(half_lt_self ht').le,by linarith⟩
    obtain ⟨_,_,_,H,_⟩:= (hD _ he).pays; obtain ⟨r,hq,hR⟩:= H.stamp.boundE; obtain ⟨a,h,hF⟩:= H.pays
    have hr(y:ℝ)(x:ℝ)(h:0<x)(p:ℝ): ∀ᶠ z in 𝓝[T] y, ‖y/t-z/t‖*p<x:=by
       let f z:= ‖y/t-z/t‖*p; have hp:(f y)=0:=by unfold f; ring_nf; simp
       exact (((show Continuous f from (by unfold f; fun_prop)).continuousAt).eventually (gt_mem_nhds (hp.trans_lt h))|>.filter_mono nhdsWithin_le_nhds)
    constructor
    · intro x hx i ε hε; filter_upwards [hr x ε hε (r i), self_mem_nhdsWithin] with y hy hY
      rw [Frost.coatE (t:=t) _ _ _ _ _ _ ht'.ne', Frost.coatE (x:=y) (t:=t) _ _ _ _ _ ht'.ne']
      refine ⟨hε.le,fun U hU l hl ha=>?_⟩; rw [Start.left_mult, Start.left_mult,← sub_mul,norm_mul]; exact (mul_le_mul_of_nonneg_left (hq i|>.2 U hU l hl ha) (norm_nonneg _)).trans hy.le
    apply Payments.steady (d:=fun x=> V x) (fun x hx i=>?_ ) (fun x hx i=>⟨?_,?_⟩)
    · obtain ⟨_,_,_,h,_⟩:= (hD x hx).pays; obtain ⟨f,ht,hF⟩:= h.pays; exact ⟨_,hF i⟩
    · intro ε he; filter_upwards [hr x ε he (a i)] with y hy U
      rw [coatL (t:=t) _ _ _ _ _ _ ht'.ne', coatL (x:=y) (t:=t) _ _ _ _ _ ht'.ne']; simp only [Pi.smul_apply, smul_eq_mul, ← sub_mul,norm_mul]; exact (mul_le_mul_of_nonneg_left (hF i U) (norm_nonneg _)).trans hy.le
    intro ε he; let u y:= ‖x-y‖*Start.total n; have hp:u x=0:=by simp [u]
    filter_upwards [((show Continuous u by unfold u; fun_prop).continuousAt.eventually (gt_mem_nhds (hp.trans_lt he))|>.filter_mono nhdsWithin_le_nhds), self_mem_nhdsWithin] with y hy hY U; exact (Start.forced_dist hb.direct ((half_pos ht').le.trans hx.1) ((half_pos ht').le.trans hY.1) i U).trans hy.le
include hl
lemma onR : Curve p (fun x=> finish (Design.top G c) c p W (iceCap G M p c x κ) x 0) T:=by
    refine ⟨continuous_id.continuousOn,continuousOn_const,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,?_⟩
    intro ε he x hx; let y:= bank n G M; let t':= y.encoding.some
    filter_upwards [(Frost.wick G M p c hb ht hD).measured (Frost.prelude G M p c hb ht hD hl) t' hx ε he,self_mem_nhdsWithin] with z hz hZ
    exact ((hD _ hx).address (Design.top G c) c x 0 t').compares ((hD _ hZ).address (Design.top G c) c z 0 t') hz
end YM.WilsonStartup.Frost

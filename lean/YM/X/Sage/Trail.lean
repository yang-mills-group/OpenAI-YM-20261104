import YM.X.Sage.Lim
import YM.X.Try.Breeze
/-!
# readers: point filter.Pulse.Region.Canonical lower billing.Width. Pure/Wick.Fl.E.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund Imprint
open Stems hiding X
open MeasureTheory Bare MvPolynomial Set Pulse Pert Pert.Position Pert.RawLabels Labels Maxwell.Free
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {m d k:ℕ} {V I:Type*} {q:ℕ+} {r R:ℝ}
local notation "τ"=>(atTop: Filter ℕ)
local notation "E"=>Pert.Position.E F d
local notation "ε"=> epsilon q k
local notation "o"=> side q k
variable (S:Bare.Shop F)(v:Fin m → Pert.Position.E F d)(hq:1<q.val)(t: Test m) (a:Beam q)
abbrev postZ (S:Bare.Shop F)(v:Fin m→Pert.Position.E F d)(X: Fin m→ Fielding.Walk)(q:ℕ+)(a:Beam q) (k:ℕ):ℂ:= partM S (side q k) (epsilon q k) (postal X (a k) k) d 0 v
abbrev foamy (v:(i:ℕ)→Grid.offsets q m i):Fin m→Fielding.Walk:= fun j k=> lift (v k j)
lemma hose (v:(i:ℕ)→Grid.offsets q m i): postal (foamy v) (a k) k= storefront q k (v k) (a k):= by ext1 j; simp only [postal,Crate.Fund.stock,foamy, wrap_lift]
include hq
lemma sample_i (s:(i:ℕ)→Grid.offsets q m i)(t:Points m)(h:clockP t s) (i:Fin m): plot q (foamy s i) (t i):= Grid.sample_each hq h i
lemma metric_cost (s:(i:ℕ)→Grid.offsets q m i)(t:Points m)(h:clockP t s)(ha:∀ i:ℕ,a i∈origins q i):
    CostF (fun k=> outerK S (epsilon q k) (postal (foamy s) (a k) k) d 0 v) (postZ S v (foamy s) q a):= by
    unfold CostF; let u(j:Fin m):Beam q:=fun i=> postal (foamy s) (a i) i j; refine (approach_zero S u a (at_origin a ha) (fun i=>on_neighbor a (foamy s i) (sample_i hq s t h i)) hq v).goes hq -- Beam.n
abbrev Guide (K:Bare.Shop F)(q:ℕ+)(v:Fin m→Pert.Position.E F d) : Prop := ∀ x:Points m,x∈conf m→∀ X:Fin m→Fielding.Walk,(∀ i, plot q (X i) (x i))→∀ a: Beam q, Tendsto (postZ K v X q a) τ (𝓝 0)
lemma seam (h:Guide S q v): pureBank F d m t v=0:= by
    let f(i:ℕ)(a:Native q i)(v':Grid.offsets q m i) := score (epsilon q i) t (Grid.sample q i v') * outerK S (epsilon q i) (storefront q i v' a) d 0 v;
    have he : Tendsto (fun i:ℕ=>S.bank q i d 0 m t v) τ (𝓝 (pureBank F d m t v)) := S.bank_white q hq (s:=⟨m,v,t⟩); apply tendsto_nhds_unique he; simp_rw [bank_time]; have hh (a:Beam q)(ha:∀i,a i∈origins q i)(x:Points m)(hx:x∈Curve t)(v':(i:ℕ)→Grid.offsets q m i)(hv:clockP x v'): Tendsto (fun i=> f i (a i) (v' i)) τ (𝓝 0):= by
        have he: Tendsto (fun i=>outerK S (epsilon q i) (postal (foamy v') (a i) i) d 0 v) atTop (𝓝 0):= CostF.goes (metric_cost S v hq a v' x hv ha)|>.2 (h x (conf_curve t hx) (foamy v') (sample_i hq v' x hv) a); unfold f; simp_rw [← hose a v']; simpa using! (Tri.score_trk t hq v' hv).mul he
    have hv:= (pay_integral hq f (region_compact t) hh (g:=fun _=>0) (fun _ _=>rfl) (fun v' w x hh=>by unfold f; rw [score_dead t hq hh, zero_mul])).2; rw [integral_zero] at hv; exact hv
lemma geo_live {x y: E4}{X Y:Fielding.Walk}(h:x≠y)(hx:plot q X x)(hy:plot q Y y): ∀ᶠ r:ℝ in 𝓝[>] (0:ℝ),Clear q r X Y:= by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr h)))] with z hz; exact ⟨x,y,hx,hy,hz⟩
omit hq
lemma furnish (F:Fin 3→Fielding.Walk): Geom.head (F 0) (F 1) (F 2)=F := by ext1 i; fin_cases i <;> rfl -- F type Walk F
local notation "rN" => dean F (show 4 ≤ 6 from by decide)
lemma lower_u (h:4≤d): dean F h∈ lower F 4 d:= by
    rw [← SetLike.mem_coe, ← stairs_eq F 4 d]; exact ⟨UW G h, rfl,(UW G (Nat.le_refl 4)).property⟩
def measureS (F:Frames G)(t:Test 3): Splot F:= ⟨3,0,talent F (Nat.le_refl 6),by intro j hj; fin_cases j <;> first| (exact (hj rfl).elim)|(exact lower_u _),t⟩ -- uses ω proof
local notation "B₀"=> talent F (Nat.le_refl 6)
local notation "W"=> μDeck q G
include hq
set_option maxHeartbeats 480000 in
lemma soul (u:Pert.Position.E F 6) : Guide S q (Function.update B₀ 0 u):= by
    intro x hx X hX a; obtain ⟨r,hr,h1,h2,h3⟩:= ((show ∀ᶠ r:ℝ in 𝓝[>] 0,(0:ℝ)<r from self_mem_nhdsWithin).and ((geo_live (hq:=hq) ((show Injective (WithLp.ofLp x) from hx).ne (show (0:Fin 3)≠1 by decide)) (hX _) (hX _)).and ((geo_live hq ((show Injective (WithLp.ofLp x) from hx).ne (show (1:Fin 3)≠2 by decide)) (hX _) (hX _)).and (geo_live hq ((show Injective (WithLp.ofLp x) from hx).ne (show (2:Fin 3)≠0 by decide)) (hX _) (hX _))))).exists -- count
    let z:=X 0; let p:=X 1; let y:=X 2; have hg: Geom q r z p y:= ⟨h1,h2,h3⟩; obtain ⟨χ⟩:= Floor.make (R:=r/2) (by linarith); let b:= Function.update B₀ 0 u; let T:= Tot.pV S q 6 b
    unfold postZ; simp_rw [initial_est S q X]; change Tendsto (gather q z p y (T 0) (T 1) (T 2)) τ (𝓝 0); let U: Foam G:= stance S q 6 (UW G (by decide)); have he : T 1= U:= by change stance S q _ ((physicalLabel F 6) (b 1))=_; unfold b; rw [Function.update_of_ne (show (1:Fin 3)≠0 from by decide)]; exact congr_arg _ (dean_c F _)
    rw [he, show T 2=T 1 from ?_, he]; swap; · unfold T Tot.pV handV b; simp only [Function.comp_apply,Function.update_of_ne (show (1:Fin 3)≠0 from by decide),Function.update_of_ne (show (2:Fin 3)≠0 from by decide)];rfl
    have ha:Apt q r (T 0):= illA _ _ (stan_h S hq _) hq hr; refine CostF.sterile (CostF.trans (replace_fields q z p y hg hr hq ha (a:=U) (b:=U) (feelU hq S _) (feelU hq S _) (single_ready degreeU) (stan_h S hq _)) (CostF.zero (arrest z p y χ hg (by linarith) hq ha (fun i=> tag_stanza S _)))) -- namespace
include S
lemma lumen (t:Test 3): sterile (measureS F t):= by apply LinearMap.ext; intro p; exact seam S _ hq t (soul S hq p)
end YM.PositionX.Sage

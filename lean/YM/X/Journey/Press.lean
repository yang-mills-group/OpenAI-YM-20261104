import YM.X.Journey.Oven
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
variable {m:ℕ}(t:Test m)(hq:1<q.val)
open Subcell
-- spell
local notation "KeA"=>Grid.offsets q m
local notation "Fℕ"=>(atTop:Filter ℕ)
def score (r:ℝ)(t:Test m)(p:Points m):ℂ:= Complex.ofReal (sweep (Complex.re ∘ t) r p)+Complex.I* Complex.ofReal (sweep (Complex.im ∘ t) r p)
def Curve (t:Test m):= valley (tsupport t)
lemma region_compact : IsCompact (Curve t):= valley_compact t.hasCompactSupport
lemma conf_curve : Curve t⊆ conf m:=valley_conf t.tsupport_subset
lemma score_cont : Continuous (fun (p:ℝ×Points m)=>score p.1 t p.2) := (Complex.continuous_ofReal.comp (sweep_ok _ (Complex.continuous_re.comp t.continuous))).add ((Complex.continuous_ofReal.comp (sweep_ok _ (Complex.continuous_im.comp t.continuous))).const_mul _)
@[simp] lemma score_origin (x:Points m): score 0 t x=t x:= by rw [score,no_sweep,no_sweep,mul_comm];exact Complex.re_add_im ..
include hq
lemma score_dead {x:Points m}(h:x∉Curve t) : score (epsilon q k) t x=0:= by
    have ht : epsilon q k∈ Icc 0 1:= ⟨(epsilon_pos q k).le,small q k⟩; have hx(i)(h:i∉ tsupport t):t i=0:= image_eq_zero_of_notMem_tsupport h; unfold score; rw [sweep_in ht (fun i hi=>?_ ) h,sweep_in ht (fun i hi=>?_ ) h]; simp; all_goals simp [hx _ (by assumption)]
omit hq
variable (b:Beam q)(p:Site (side q k))(v: Grid.offsets q m k)
-- mesh ∫. scalar version, Lo update
variable {I:Type*}[Fintype I]
def payL (q:ℕ+)(m i:ℕ)(f:Native q i→ Grid.offsets q m i→ℂ):ℂ:= (((origins q i).card:ℝ)⁻¹ ) • ∑ p∈ origins q i, epsilon q i ^ (4*m) • (∑ v:Grid.offsets q m i, f p v)
local notation "trustF"=> Buffer F d
variable (f:(i:ℕ)→Native q i→ Grid.offsets q m i→ ℂ) {g:Points m→ℂ}{K:Set (Points m)}
include hq
lemma pay_gate (hK:IsCompact K) (h:∀ a:Beam q,(∀i,a i∈origins q i)→∀ x∈K,∀ v:(i:ℕ)→Grid.offsets q m i,clockP x v→ Tendsto (fun i=>f i (a i) (v i)) Fℕ (𝓝 (g x))) (hp:∀ x∉K,g x=0)(hw:∀i:ℕ,∀a:Native q i,∀v:Grid.offsets q m i, Grid.sample q i v∉K→ f i a v=0): Released (fun i=> payL q m i (f i)):= by
    let value (L':ℂ →L[ℝ] ℝ):= ∫ x:Points m,L' (g x); have he (L':ℂ→L[ℝ] ℝ) : Tendsto (fun i=> L' (payL q m i (f i))) Fℕ (𝓝 (value L')):= by
       simp_rw [payL,map_smul,map_sum,map_smul,map_sum]; apply Grid.average_paths (f:=fun m' o=>epsilon q m'^(4*m)*∑ v:Grid.offsets q m m', L' (f m' o v)) (hn:=fun i=> hasOrigin q i);
       intro a ha; exact (Grid.integrable_spots hq (K:=K) (F:=fun i v=>L' (f i (a i) v)) (fun s x hx hs=> L'.continuous.continuousAt.tendsto.comp (h a ha x hx s hs)) hK (fun i k ht=>by rw [hw _ _ _ ht,map_zero]) (T:=fun x=>L' (g x)) (fun i hi=>by rw [hp i hi,map_zero])).2
    exact ⟨⟨value Complex.reCLM,value Complex.imCLM⟩, touchℂ (by exact he Complex.reCLM) (by exact he Complex.imCLM)⟩
abbrev tallyM (p:Test m)(q:ℕ+)(i:ℕ)(g:(Fin m → Site (side q i))→ℂ):ℂ:= payL q m i (fun a v=>score (epsilon q i) p (Grid.sample q i v)*g (fun j=>v j+a))
variable {r:ℝ}
local notation "V₀" i:arg x=>kin S x (epsilon q i) (barter (q:=q) (k:=i) (d:=d) S w)
lemma score_grid {x:Points m}{v:(i:ℕ)→Grid.offsets q m i}(hv:clockP x v): Released (fun i=> score (epsilon q i) t (Grid.sample q i (v i))):= by
    have he : Tendsto (fun i=> (epsilon q i, Grid.sample q i (v i))) atTop (𝓝 ((0:ℝ),x)):= (paths hq).cutoff.prodMk_nhds hv
    let f(p:ℝ × Points m) := score p.1 t p.2; change Released (f ∘ (fun i=> (epsilon q i, Grid.sample q i (v i)))); exact ⟨_,Tendsto.comp ((score_cont t).tendsto (0,x)) he⟩
lemma walks_budget (hr:R<r)(hg:G.Simple)(hK:Curve t⊆Region m r)(p:Fin m→ E d): Released (fun i=> tallyM t q i (fun x=>(V₀ i x) p)):= by
    let f(i:ℕ)(a:Native q i)(v:Grid.offsets q m i):= score (epsilon q i) t (Grid.sample q i v)* teamK S i a v d w p; have ht(x:Points m)(h:x∈ Curve t):∃ C:ℂ,∀a:Beam q,(∀ i,a i∈origins q i)→∀ s:(i:ℕ)→Grid.offsets q m i,clockP x s→ Tendsto (fun i=> f i (a i) (s i)) Fℕ (𝓝 C):= by
       apply single_gate f x hq; intro a ha v hv; exact Shelf.breaths (score_grid t hq hv) (walks_visit S w a ha hq v x r hr hv p hg (hK h)); -- arguments
    let g(x:Points m):= if h:x∈ Curve t then (ht x h).choose else 0; apply pay_gate hq f (g:=g) (region_compact t); intro a ha x hx s hs; unfold g; rw [dif_pos hx]; exact (ht x hx).choose_spec a ha s hs; intro x he; exact dif_neg he; intro i a v h; unfold f; rw [score_dead t hq h,zero_mul]
end YM.PositionX.Pulse

import YM.X.Journey.Tome
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
section tools
local notation "Fℕ"=>(atTop:Filter ℕ)
variable {Ω:ℕ→Type*}(p:ℕ→Prop)[DecidablePred p][TopologicalSpace V] {v:V}
def weave (a b:(i:ℕ)→ Ω i): (i:ℕ)→Ω i:= fun i=> if p i then a i else b i
lemma tend_weave (f:(i:ℕ)→ Ω i→ V){a b:(i:ℕ)→ Ω i} (h:Tendsto (fun i=>f i (a i)) Fℕ (𝓝 v))(hp:Tendsto (fun i=> f i (b i)) Fℕ (𝓝 v)): Tendsto (fun i=> f i (weave p a b i)) Fℕ (𝓝 v):= by
    apply tendsto_def.mpr; intro s hs; filter_upwards [h hs,hp hs] with i hi hk; change f i (weave p a b i)∈s; unfold weave;split;exact hi;exact hk
private def switch' (i:ℕ):= i % 2 = 0
-- ℂ or T2
lemma coincide [T2Space V] {h:V}{A' : Set ((i:ℕ)→ Ω i)}(HA:∀a∈A',∀ b∈A',∀ (p:ℕ→Prop), weave p a b∈A'){a b:(i:ℕ)→ Ω i}(f:(i:ℕ)→ Ω i→ V)(ha:a∈ A')(hb:b∈A')(hx:Tendsto (fun i=>f i (a i)) Fℕ (𝓝 v))(hy: Tendsto (fun i=>f i (b i)) Fℕ (𝓝 h))(hv:∀a∈ A',∃ v:V,Tendsto (fun i=>f i (a i)) Fℕ (𝓝 v)): v=h:= by
    classical
    let q:=switch'; let s:= weave q a b; obtain ⟨C,hc⟩:= hv s (HA a ha b hb q)
    have ht:Tendsto (fun k:ℕ=>k+k) Fℕ Fℕ:= StrictMono.tendsto_atTop (fun i j h=>by omega)
    have hz:Tendsto (fun k:ℕ=>k+k+1) Fℕ Fℕ:= StrictMono.tendsto_atTop (fun i j h=>by omega)
    apply Eq.trans (tendsto_nhds_unique (hx.comp ht) ((hc.comp ht).congr ?_)) (tendsto_nhds_unique ((hc.comp hz).congr ?_) (hy.comp hz)); -- tactic goal order
    all_goals (intro i; simp only [comp_apply,s]; unfold weave q switch';split<;>first|rfl|omega)
section cell
variable {m:ℕ}
variable (f:(i:ℕ)→ Native q i→ Grid.offsets q m i→ ℂ)(x:Points m) (hq:1<q.val)
abbrev P₀ (q:ℕ+)(m:ℕ) (i:ℕ):= Native q i × Grid.offsets q m i
local notation "Tc"=> P₀ q m
abbrev clockP (x:Points m) (s:(i:ℕ)→Grid.offsets q m i):= Tendsto (fun i=> Grid.sample q i (s i)) Fℕ (𝓝 x)
def VisaL (q:ℕ+)(m:ℕ)(x:Points m):Set ((i:ℕ)→P₀ q m i):= {s|(∀i,(s i).1∈origins q i)∧ clockP x (fun i=> (s i).2)}
lemma visa_path (p:ℕ→Prop)(a b:(i:ℕ)→P₀ q m i)(ha:a∈ VisaL q m x)(hb:b∈ VisaL q m x): @weave _ p (fun i=> Classical.propDecidable _) a b ∈ VisaL q m x:= by
   classical
   refine ⟨fun i=>?_, tend_weave (a:=a) (b:=b) (p:=p) (f:=fun i (a:P₀ q m i)=> Grid.sample q i a.2) ha.2 hb.2⟩; unfold weave; split; exact ha.1 i;exact hb.1 i
include hq
lemma single_gate (h:∀ a:Beam q,(∀i,a i∈ origins q i)→∀ b:(i:ℕ)→ Grid.offsets q m i, clockP x b→ Released (fun i=> f i (a i) (b i))): ∃ C:ℂ,∀ a:Beam q,(∀i,a i∈ origins q i)→∀b:(i:ℕ)→ Grid.offsets q m i, clockP x b→ Tendsto (fun i=> f i (a i) (b i)) Fℕ (𝓝 C):= by
    have he':∀ a∈ VisaL q m x,Released (fun i=> f i (a i).1 (a i).2):=fun a ha=> h _ ha.1 _ ha.2; choose a ha using fun i=> hasOrigin q i; obtain ⟨C,hc⟩:= h a ha (fun i=>Grid.signal q i x) (Grid.choose_sample hq x); refine ⟨C,?_⟩; intro A' h' b hb; obtain ⟨d,hd⟩:= h A' h' b hb
    rwa [show C=d from coincide (A':=VisaL q m x) (fun a ha b hb p=> visa_path x p a b ha hb) (a:=fun i=>(a i,Grid.signal q i x)) (b:=fun i=>(A' i,b i)) (fun i v=>f i v.1 v.2) ⟨ha,Grid.choose_sample hq x⟩ ⟨h',hb⟩ hc hd he']
end cell
lemma touchℂ {f:ℕ→ℂ}{r:ℂ}(h:Tendsto (Complex.re ∘ f) Fℕ (𝓝 r.re))(hy:Tendsto (Complex.im ∘ f) Fℕ (𝓝 r.im)): Tendsto f Fℕ (𝓝 r):= by
    have hx:=(Complex.continuous_ofReal.continuousAt.tendsto.comp h).add ((Complex.continuous_ofReal.continuousAt.tendsto.comp hy).mul_const Complex.I); rw [Complex.re_add_im] at hx; exact hx.congr fun _=>Complex.re_add_im _
end tools
end YM.PositionX.Pulse

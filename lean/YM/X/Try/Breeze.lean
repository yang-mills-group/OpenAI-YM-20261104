import YM.X.Try.Tress
/-!
# Payoff for prepared α-diagnostics. Simple lower even tomography.
Clearance ∀ᶠ r then ANY single mark Floor strictly below r used in all provisional shifts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Maxwell Maxwell.Free MvPolynomial Function Set Filter MeasureTheory Asymptotics
open PertExtension LatticePT Next.Rank Next.Rank.Normal
open Pert Pert.Position Pert.RawLabels Pulse Bare Ribbon Detector
open Interval.Size Hinge Reed Stems Haze Interval
open Jet hiding Word
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{F:Labels.Frames G}{d k m:ℕ} {V W I:Type*} {r R:ℝ}
variable (S:Bare.Shop F)(hq:1<q.val)(hg:G.Simple)(w:Floor R) (hr:R<r)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ℒ"=> Pert.Position.lower F 4 6
local notation "D"=> nested F hg S 6
local notation "A₁"=> main q S
local notation "B"=> Bank F 6
local notation "Y"=> Splot.result F
local notation "ξ"=> Splot.sit F
local notation "γ"=> YM.PositionX.par F 6
local notation "ℝ₀"=> Pulse.Region
local notation "b·" => pureBank F 6
def ready (r:ℝ):Prop:= (∃ n:ℕ,∃ s:Fin n→Splot F, LinearMap.ker (LinearMap.pi (fun i=> Y (s i) b· ∘ₗ (halfling F).subtype))=⊥∧∀ i:Fin n,width (s i) r) ∧∀i:(D).rail.reached, Curve ((D).rail.reachedV i).f⊆ ℝ₀ ((D).rail.reachedV i).r r
abbrev xAway (S:Bare.Shop F)(q:ℕ+)(w:Floor R)(i:ℕ): Workroom F 6:= Pulse.away (q:=q) (k:=i) S w 6
abbrev shapeX (S:Bare.Shop F)(q:ℕ+)(w:Floor R)(i:ℕ):Bank F 6:= remit q S (xAway S q w) i
lemma prepared_at : ∀ᶠ r:ℝ in 𝓝[>] 0, ready S hg r := by
    obtain ⟨k,s,h⟩:= pointed (F:=F) hg; have ha (k:ℕ)(t:Test k):= region_time (region_compact t) (conf_curve t); filter_upwards [eventually_all.mpr (fun i:Fin k=> ha _ (s i).test), eventually_all.mpr (fun i:(D).rail.reached=> ha _ ((D).rail.reachedV i).f)] with r hs hu; exact ⟨⟨k,s,h,hs⟩,hu⟩
theorem press_early (x: E F 6)(s:Splot F) (hx:γ x= -x) (hs: sterile s) (H: ready S hg r) (hv: width s r)
    (hr:R<r): Tendsto (fun i=> Y s (shapeX S q w i) x) Fℕ (𝓝 (Y s (firstX S q hq hg 6) x)) := by
    obtain ⟨⟨n,v,H,hv'⟩,h⟩:= H; have he := no_drift S hq hg w hr hx s v H hv' hs; have he': Tendsto (fun i=>Y s (shapeX S q w i) x-Y s (A₁ i 6 w 1) x) Fℕ (𝓝 0):= he; have hh:= (he'.add (fade S hq hg w hr hx s h hs hv)).add (show Tendsto (fun i=> Y s (S.uncut hg q i 6 1) x) Fℕ (𝓝 (Y s _ x)) from limit₁ S q hq hg (ξ x s)); rw [zero_add,zero_add] at hh; apply hh.congr; intro i; abel
end YM.PositionX.Tri

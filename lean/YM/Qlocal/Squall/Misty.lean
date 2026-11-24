import YM.Qlocal.Squall.Harvest
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Squall
open Filter Function Set Lattice Wilson RG Pressure Tree Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Extra.Iteration Song
open Collection Quotes Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Roost Coat ThroughLaunch
open RGComparison01 RGComparison01.Pledge RGComparison01.Pledge.Holdings BudgetPoint
open Push.Uniform Sienna
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open AllOrder Floe Step Step.PlanV Catch Skull
variable {G:Gauge}
namespace Lumber
variable {X: Metals G} {D: Rolls X.p} {C: Targets X.p X.K} {Z: Expenses C}
    {p w:Return.Wages} {v:ℕ→ℝ} (J: PhysicalNext.Repeat.Register D Z p v)(η:ℕ→ℝ)(T:ℕ→ℕ){F:ℕ→ℕ→Postage}(S:Time.Scouts (F:=F))
variable (x y :ℕ)(he:StepStages x y)(hx:4≤x)
local notation "L"=> D.L x
local notation "V0"=> X.p.profile x
local notation "W₀"=> X.p.profile y
set_option quotPrecheck false
local notation "t₀"=> C x y
local notation "ℓ"=> Z x y
open Quipu.Sonnet Quipu.Eluder.Incline.Bookworm Dredge -- Permit unknown remove
variable (R:Roots (G:=G) X.p.profile X.K X.p.kernel)
variable (r q:ℕ)
variable {P:Protection D} (U:Delays P)
variable (ζ:ℕ→ℝ)
structure Patent (x':ℝ) (A:Bark J η T S x y hx r q) : Prop where
    sober : ∀ z≥x',Bark.Saw J η T S x y hx r q A z
    heroes : ∀ k,Burn.horizon k+2≤ y → ∀ N≤x,∀ t≤x,∀ n≤x,∀ (B: Marker.Census (Fin n)) (g:Fin n→ℕ), (∀ i,g i≤x) → 2≤N→ N≤t → (∀ s:Senses B, Quipu.Eluder.Incline.Bookworm.warrant r s g N) → Nonempty (Card D R x y hx (Burn.horizon k)) → ∃ Q: Pose D R x y (Burn.horizon k) N hx (Fin n) B g r t, ∀ z≥x',Bark.Yaw J η T S x y hx r q A R (Fin n) B g k N t Q (ζ x) z
lemma rack {V:Type}{I:Type} (f:Filter I) [Finite V] (U: (V→ℕ) → I→ Prop) (h:∀ g:V→ℕ,(∀ i,g i≤x)→ ∀ᶠ i in f,U g i): ∀ᶠ i in f,∀ g:V→ℕ,(∀ i,g i≤x)→ U g i:= by
 let ψ(a:V→Fin (x+1))(i:V):=(a i).val; filter_upwards [eventually_all (p:=fun a i=>U (ψ a) i)|>.mpr (fun a=> h _ (by intro i; have hv:=(a i).isLt; unfold ψ; omega))] with i hi g he ; exact hi (fun i=> (⟨g i,(by have h:=he i; omega)⟩:Fin (x+1)))
-- local instance census Card.Finite. proof optional.B.Info.
local instance {α:Type}[Finite α][DecidableEq α] : Finite (Marker.Census α):= Finite.of_injective Marker.Census.choices (fun {x y} h=>(by cases x; cases y; congr)) -- tactic
-- height helper for k etc.Menu Era.Qu.L.Root.
lemma piano {V:Type} (f:Filter V)(L':ℕ→V→Prop)(h:∀ k≤ x,∀ᶠ i in f,L' k i): ∀ᶠ i in f,∀ k≤ x,L' k i:= by filter_upwards [(eventually_all_finset (I:=range (x+1)) (p:=L')).mpr (fun i hi=> h i (Nat.le_of_lt_succ (mem_range.mp hi)))] with i hi k hk using hi k (mem_range.mpr (by omega))
variable (V:Bark J η T S x y hx r q)
variable (ht:(C x y).table=X.O)(hh:Prior.Awning R x (↑(D.L x).val:ℝ))(hz:0 < ζ x)
variable (α:Type)[Fintype α][DecidableEq α] (B: Marker.Census α)(g:α→ℕ) (k N t:ℕ)
set_option quotPrecheck false
local notation "Q₀"=> Pose D R x y (Burn.horizon k) N hx α B g r t
-- help later Extension.Frame.Head.Clock.Contributions.
include ht he hh hz
lemma rights (hk:Burn.horizon k+2≤ y) (hN:2≤N)(hT:N ≤t)(hF:N≤x)(hw:∀ s:Senses B,Quipu.Eluder.Incline.Bookworm.warrant r s g N)(hκ:Nonempty (Card D R x y hx (Burn.horizon k))): ∀ᶠ u in atTop, ∃ Q: Pose D R x y (Burn.horizon k) N hx α B g r t, ∀ a≥u,Bark.Yaw J η T S x y hx r q V R α B g k N t Q (ζ x) a:= by
 have hκ': y ≤ x:=he.1; obtain ⟨Q⟩:= Dredge.pose D R x y (Burn.horizon k) N hx α B g r t hw hT he hN hh hF (by omega)
 obtain ⟨c,hc⟩:= eventually_atTop.mp (Bark.yawns J η T S x y he hx r q V R α B g k N t hκ Q (ζ x) ht hz)
 exact (eventually_ge_atTop c).mono fun t ht=>⟨Q,fun a ha=>hc _ (ht.trans ha)⟩
lemma ready : ∀ᶠ s in atTop,Patent J η T S x y hx R r q ζ s V:= by
 obtain ⟨t,hT⟩:= eventually_atTop.mp (V.sandal); let κ (k:ℕ):=Burn.horizon k+2
 let U (k N t n:ℕ)(x':ℝ):=∀ (B: Marker.Census (Fin n))(g:Fin n→ℕ),(∀ i,g i≤x)→κ k≤y→2≤N→N≤t→(∀ s:Senses B,Quipu.Eluder.Incline.Bookworm.warrant r s g N)→ Nonempty (Card D R x y hx (Burn.horizon k)) → ∃ Q: Pose D R x y (Burn.horizon k) N hx (Fin n) B g r t,∀ z≥x',Bark.Yaw J η T S x y hx r q V R (Fin n) B g k N t Q (ζ x) z
 have hu(k N n t:ℕ)(h:N≤x):∀ᶠ x' in atTop,U k N t n x':= by
    refine eventually_all.mpr fun B: Marker.Census (Fin n)=> rack x atTop _ ?_; intro g hg; by_cases hP:κ k≤y; swap; · exact Eventually.of_forall fun _ he=> (hP he).elim
    by_cases hn:2≤N∧N≤t; swap; · exact Eventually.of_forall fun _ _ hh hx=> (hn ⟨hh,hx⟩).elim
    by_cases hp:(∀ s:Senses B,Quipu.Eluder.Incline.Bookworm.warrant r s g N)∧ Nonempty (Card D R x y hx (Burn.horizon k)); swap; · exact Eventually.of_forall fun _ _ _ _ he he'=> (hp ⟨he,he'⟩).elim
    exact (Lumber.rights J η T S x y he hx R r q ζ V ht hh hz (Fin n) B g k N t hP hn.1 hn.2 h hp.1 hp.2).mono fun _ hi _ _ _ _ _=>hi
 have hv(k N:ℕ)(h:N≤x): ∀ᶠ s in atTop, ∀ t≤x,∀ n ≤ x,U k N t n s := piano x atTop _ (fun t ht=> piano x atTop _ (fun n hn=> hu k N n t h))
 have hu':∀ᶠ s in atTop,∀ k≤x,∀ N≤x,∀ t≤x,∀ n ≤ x,U k N t n s:= piano x atTop _ (fun k _=> piano x atTop _ (hv k))
 filter_upwards [eventually_ge_atTop t,hu'] with s hs hv; refine ⟨fun a ha=> hT _ (hs.trans ha),fun k hk N hn t ht n hz B g hg=> hv k ?_ N hn t ht n hz B g hg hk⟩; unfold Burn.horizon at hk; have ht:y≤x:=he.1; omega
end Lumber
end YM.Qlocal.Squall

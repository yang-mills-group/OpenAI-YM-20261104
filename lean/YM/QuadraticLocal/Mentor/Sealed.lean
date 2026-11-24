import YM.QuadraticLocal.Mentor.Camp
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Mentor
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration
open ThroughLaunch Height Opera Boulevard Trio Slide Sienna Fare Lapis Coat
open Input Org Supply Roost Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Burn AllOrder.Ink AllOrder.Ink.Money
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Wheel
open AllOrder.Wheel.Ride AllOrder.Wheel.Ride.Pair AllOrder.Catch
open QuadraticLocal.Sunrise QuadraticLocal.Echo RemainderComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {V:Type}[Fintype V][DecidableEq V] {G:Gauge} {X: Metals G}
variable (R: Roots (G:=G) X.p.profile X.K X.p.kernel) (D:Rolls X.p) (Q:R.Tab D)
open AnalyticBridge.VerifiedReset
variable {Z:Targets X.p X.K} {E:Expenses Z}{p:Return.Wages}{z:ℕ→ℝ} (W: Repeat.Register D E p z) {M:ℕ→ℕ→Postage} (S: AnalyticBridge.VerifiedReset.Time.Scouts (F:=M))
set_option quotPrecheck false
local notation "Φ" x:max y:max=> (W.μ x y)
variable (ψ:ℕ→ℕ) (K0:Offices.Books R D Q ψ)
open Offices
variable {P₁:Protection D}
structure Educated (V:Delays P₁): Prop where
   enrolled (x y:ℕ)(r:Opportunity x y)(t:ℝ): V.betaEntry x ≤ t → Bought R D Q W S ψ r K0 t
   floor (x y:ℕ)(r:Opportunity x y): Radii.rentals (Z x y|>.halo) r.count r.stage≤ V.shells x
   growing (x:ℕ): 1 ≤ V.growth x
-- setup doesn't presume age compatibility across different Tabs; those Books chosen BEFORE sales. Plug other conditions after these. Level.W stamps Food.Reach use for capacity after establishing Housing. (Dependencies aren't random unrelated tab at each call.)
theorem educates (hS:Offices.Sales R D Q W S ψ K0)(V:Delays P₁): ∃ Y: Delays P₁, DelayLe V Y ∧ ∀ X':Delays P₁, DelayLe Y X' → Educated R D Q W S ψ K0 X':= by
 let f x y t:= ∀ r:Opportunity x y,Bought R D Q W S ψ r K0 t; let g x y:= fun r:Opportunity x y=> Radii.rentals (Z x y|>.halo) r.count r.stage
 have he x y:∀ᶠ t in atTop,f x y t:= eventually_all.mpr fun i=> hS.later x y i
 obtain ⟨u,-,hv,H⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j atTop _ (fun i hi=> he j i))
 letI(f g:ℕ):Fintype (Opportunity f g):= Fintype.ofFinite _
 let k(x y:ℕ):= Finset.univ.sup (g x y)
 let T:Delays P₁ := {V with betaEntry:=u,shells:=fun x=> V.shells x+fromMax k x,growth:=fun x=> V.growth x+1}; refine ⟨T,⟨hv,le_rfl,fun x=>Nat.le_add_right ..,fun x=>Nat.le_add_right ..⟩,fun U z=>⟨fun x y r t ht=> H x t ((z.beta x).trans ht) y r.meet r,fun x y r=> ?_,fun x=>(Nat.le_add_left 1 _).trans (z.growth x)⟩⟩ -- `letI` syntax
 exact (((Finset.le_sup (f:=g x y) (Finset.mem_univ r)).trans (le_fromMax k r.meet)).trans (Nat.le_add_left (fromMax k x) _)).trans (z.shells x)
end YM.QuadraticLocal.Mentor

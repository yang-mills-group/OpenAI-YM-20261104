import YM.FVA2.Hearth.Frost
import YM.RGComparison.Core16.Silk.Roll
/-!
 # Fk.read realization

 Bridge from the explicit pressure `Base` formal rule (`Fk` -- not making a
 compact-support budget estimate) to the RG10 history. Use a single Context glyph, all
 interior locs in one slot set (coordinates could be labelled by any addresses instead;
 NOT making coverage or cost claims with these dummy addresses or unused Shelf prices).
 Cost payload and Shelf implement the actual physical unmasked exponent on this prefix.
 Curvature only a coordinate used on Shelf, can verify identity on nbhd with no new
 measure factors. Branch Choices in Fabric implement shared physical tags, held fixed.
 Note the `Planet` here is not assumed `Steady`; that would require additional
 data. See `Embr/Provider.lean` for an enriched implementation **including** such
 an instance (but still fixed-geometry, no estimate claims on the overall `Run`). Here instead prove by direct jet & native covariance/
 realized square, with the hypothesis `ChartRatio`, and have proved coercivity and even
 whole-stamp Haar/Laplace aspiration at each fixed geometry when needed.

 Using formal **prefix** of any length, including of length one for an incoming Wilson
 step. This implements the ACTUAL FORMAL inversion quotient problem in Fk; don't infer
 identities between coefficients with the cover periodic non-inversion Planet. Constants
 can depend on the whole prefix and final coarse link values.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open RGComparison.Core16.Lumen RGComparison.Core16.Forge
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}{L:Fabric G n}(T:Cloth L)(y:Flats G (Bottom L))
variable (x:G.ColorIndex)(w:L.Accounts→ℝ→ℝ)
local notation "X₀"=>Warm T
local notation "F"=> Facade.Panel T

lemma occupied (s:G.Simple): Nonempty G.ColorIndex:= by
 by_contra! he; haveI : IsEmpty G.ColorIndex:= he; haveI:= Gauge.Simple.nontrivial_color s
 obtain ⟨x,y,H⟩:= exists_pair_ne G.Color; exact H (by ext i; exact isEmptyElim i)

-- store ray in a true Color bin. choice of normalization cancels.
 def primeBook : Lumen.Shelf G Unit (Warm T) := { sector:=⟨1,1,1,Nat.zero_lt_one,one_pos⟩,
                                                    U:=fun _ a=> front T w y (a.1 x) (fun i=> Lumen.launch (a.2 i)),
                                                    R:=2, δ:=1, knot:=1, Q:=1 }

 def localClimate : Planet (primeBook T y x w) n (Warm T) Unit Unit where
    loc _ := 0
    root _ := 0
    meter _ _ _ := 1
    cost r _ a _ := front T w y r a
    glyph := id
    stem _ := some
    ray _ := Lumen.colors G x
local notation "P"=> localClimate T y x w
lemma climate_cost (r b a) : ((P).F r).action b a= front T w y r a := by simp [Planet.F,Base.action,localClimate]
lemma prepaid (r a) : (P).bureau r a=Real.exp (-front T w y r a /r^2):= by unfold Planet.bureau Base.output Base.cash; rw [Fintype.sum_unique,climate_cost]; exact one_mul _
-- not claiming thermo poly converges; actual probability readings for each given w and y
lemma climates (r:ℝ)(hr:r≠0): fuel T w y r = Real.exp (-1) • (P).bureau r := by ext1 a; rw [Pi.smul_apply,prepaid]; unfold fuel; change _= Real.exp _ * Real.exp _; rw [←Real.exp_add]; congr 1; field_simp; ring

lemma bookings (a: Lumen.Fk.Door G (Warm T)) (b:Unit):
  (P).load b a.1 (Lumen.Fk.spread a.2)=(a.1 • (Lumen.colors G x),fun i=> Lumen.turn (a.2 i)):= rfl

lemma xseat (a:ℝ): (a • (Lumen.colors G x) : G.Color) x=a:= by simp

local notation "H"=> Facade.raise (Facade.rate T) w y
-- purpose formula of actual expense verified GERM
lemma era : Fk.rise P =ᶠ[𝓝 0] H:= by
 have hh(i:Warm T): ∀ᶠ v:(ℝ×F) in 𝓝 0,Lumen.launch (Lumen.turn (v.2 i))=G.lieExp (v.2 i):= by
     have he:= (show Continuous (fun v:ℝ×F=>G.lieExp (v.2 i)) from by fun_prop).tendsto 0; simp only [Prod.snd_zero,Pi.zero_apply,G.mat_lieExp_zero] at he; exact he.eventually (@Lumen.leaving G)
 filter_upwards [eventually_all.mpr hh] with v (hv:∀ i,_= _) -- inspect
 change v.1^2 + (∑ i,Fk.postage P v i) = _; rw [Fintype.sum_unique]
 rcases v with ⟨s,a⟩; unfold Fk.postage; rw [bookings,truePrice]; apply congr_arg (s^2 + ·)
 change front T w y ((s • (Lumen.colors G x) : G.Color) x) (fun i=>Lumen.launch (Lumen.turn (a i)))= _
 rw [xseat,funext hv]; rfl

-- Fk cap for arbitrary prefix observables. Use master valuation identity with compatibility witness in form of a cost equality at SHELF scene; apply to literal stencils in next file.
variable {I:Type}
 def Contains (p:Lumen.Stuff G (Warm T) I)(Ψ:(I→ G.Color)→ℝ)(A:Entry T→ℝ):Prop:= Ψ ∘ (Fk.scene p) =ᶠ[𝓝 0] (A ∘ (Facade.flank y))
variable {p:Lumen.Stuff G (Warm T) I}{ψ:(I→ G.Color)→ℝ}{A:Entry T→ℝ}
variable {J:ChartRatio G}(hj:LocalRatio J)
lemma launch_me (h: Contains T y p ψ A): PowerSeries.mk (Fk.harvest P J p ψ)= Facade.constit T w y J A := by
 refine congr_arg PowerSeries.mk (congr_fun (Therm.stamp_protect _ _ _ ?_ (era T y x w)) 1)
 unfold Fk.cap coat; exact (EventuallyEq.refl (𝓝 0) (jacobian J ∘ (@LinearMap.snd ℝ ℝ F _ _ _ _ _))).mul h  -- easier
lemma launch_vacant : PowerSeries.mk (Fk.birth P J)= Facade.constit T w y J 1:= launch_me T y x w (ψ:=fun _:Empty→G.Color=>1) (p:=Fk.vacant) (EventuallyEq.refl _ _)

variable (z:L.Accounts→PowerSeries ℝ)(hz:∀ i,0< term (z i) 0)
variable (N:ℕ)(hw:∀ i,ContDiffAt ℝ ω (w i) 0)(h:∀i,Through N (Facade.amount (w i)) (z i))
include h hw hz hj
lemma feasible : 0<Fk.birth P J 0:= by
 have he:= entrance T z hj hz w y hw N h; rwa [←launch_vacant T y x w, ← coeff_zero_eq_constantCoeff_apply, coeff_mk] at he
omit hj in
lemma rise_stamina : Laplace.Steep (Fk.rise P):= Laplace.Steep.germ (steep T z hz w y hw N h) (era T y x w).symm

local notation "ξ"=> Stack.read y (sticker T z hz (J:=J) (Stack.rise A))
lemma accredited (hY:Contains T y p ψ A) (hv:ContDiffAt ℝ ∞ A 0) :
 Through N (PowerSeries.mk (Fk.valuation P J p ψ)) ξ:= by
 unfold Fk.valuation divide; rw [Tracks.asSeries,launch_me T y x w hY,launch_vacant]; exact marked T y z hz hj w N hw h A hv
lemma posts (hY:Contains T y p ψ A)(hv:ContDiffAt ℝ ∞ A 0)(a i:ℕ)(hi:a+i≤N):
 Fk.read P J p ψ a i= coeff (a+i) ξ:= by rw [←accredited T y x w hj z hz N hw h hY hv _ hi,coeff_mk]; rfl
end YM.FVA2.Hearth

import YM.MSbar.Rolling.Skirt
import YM.Work.F04.Choices
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set Next.SectorChange
open Push Push.Uniform RG Wilson Gauge Lattice Tree Precision Metric
open Exterior
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge}{c f:Side}{S: StepData c f}(B: Forest S.ratio)(i:S.Choices)(R T:PathData G)(p q:Clip)(ρ:fieldDir G c 1→ AxisChart G B)
open Cacao Bakery Portal
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "µ"=> PowerSeries.coeff
local notation "ol"=>fieldDir G c 1
local notation "X"=> Positions (Primary c G)
local notation "N"=> Positions (Primary f G)
local notation "Y"=> Positions (Key B G)
local notation "Z"=> Positions (Joint B G)
local notation "V"=> Config G f
local notation "K"=> Push.Uniform.block (priced B i p R) 0
local notation "ν"=> center B ρ
-- Binder explicit!
noncomputable def swung (J:ChartRatio G)(z: Positions (Joint B G)) := capitalJ J ((pushG B) z)
abbrev νof (S: StepData c f)(p:Clip)(R: PathData G) :=height f p R
noncomputable abbrev Nesting (G:Gauge)(n:Side) := PowerSeries (Pot (Primary n G))
noncomputable abbrev StageV (G:Gauge)(B:Forest S.ratio):=PowerSeries (Pot (Joint B G))
noncomputable def taps (G:Gauge): Matrix (Primary f G) (Joint B G) ℝ := LinearMap.toMatrix' (((stamp B G).comp (pushG B)).toLinearMap)
abbrev barbed (J:ChartRatio G)(A:Nesting G f) : PowerSeries (Pot (Joint B G)) := splitV (singularity (swung B J) 0) -splitV (singularity (pushChart B G i) 2) +PowerSeries.map (rail (taps B G)).toRingHom A
lemma well (J:ChartRatio G)(A:Nesting G f)(h : Kind A): Kind (barbed B i J A):=by unfold Kind barbed; rw [map_add,map_sub,PowerSeries.coeff_map, h,map_zero,splitK,splitK]; simp
local notation "z!"=> Function.const
variable (J:ChartRatio G)(hJ:LocalRatio J)
include hJ
lemma swung_cont : ContDiffAt ℝ ω (swung B J) 0:=by
   let f: Z→L[ℝ] LogArray G B.Free := (tint G _).toContinuousLinearMap.comp (pushG B)
   have h(k) : ContDiffAt ℝ ω (fun z:Z=> J.J (f z k)) 0:= by
       let F:Z→L[ℝ] G.Color := (ContinuousLinearMap.proj k).comp f; exact (show ContDiffAt ℝ ω J.J (F 0) from (by rw [map_zero]; exact hJ.germ _ (Metric.mem_ball_self hJ.patch))).comp _ F.contDiff.contDiffAt
   let g(z):=pay J (f z); have he:ContDiffAt ℝ ω g 0:= contDiffAt_prod (fun i _=>contDiffAt_const.mul (h i)); have ht : g 0≠0 := by rw [show g 0=pay J (0:LogArray G B.Free) from (map_zero f) ▸ rfl]; exact (crispG J hJ).ne'
   exact (he.log ht).sub contDiffAt_const
variable (n:ℕ)(A: PowerSeries (Pot (Primary f G)))(F:ℝ → Config G f→ℝ) (u v:ℕ)
-- Price hesses.Anchor. arbitrary log index. requires centered F powers
structure Trend (F:ℝ → Config G f→ℝ)(A:PowerSeries (Pot (Primary f G)))(R:PathData G)(p:Clip)(u:ℕ) : Prop where
   bond : Kind A
   plane : Expanse A 1 u
   base : ∀ᶠ t:ℝ in nhdsWithin 0 (Ioi 0),Touch (F t) ∧ F t 1=1
   control : ∃ n₀:ℕ,∃ a:ℝ,0<a∧∀ᶠ t in nhdsWithin 0 (Ioi 0),∀ i:Config G f,F t i≤ Real.exp (-a*Wilson.energy i/t^2)/ t^n₀
   quiet : Premier (main f p R)
   tune : ∀ n:ℕ,Price (yard (E:=Positions (Primary f G)) n) (u+1) (fun x y=> (Real.log (F x (postcard G f x y))+height f p R y)-taste u (picture y A) x)
local notation "E'"=> barbed B i J A
variable (hc : Serves S G)(hP:Critical B p R ρ)(hQ:ClassicalMatch B p q R T ρ)
include hc
abbrev measureK (F:ℝ → Config G f→ℝ)(t:ℝ)(x:Positions (Primary c G))(y:B.Slice G):= hut S (t⁻¹^2) (F t) (B.drape y) (postcard G c t x)
noncomputable def siteK (ρ:fieldDir G c 1→AxisChart G B)(t:ℝ)(x:Positions (Primary c G))(y:Positions (Key B G)) := capitalF (center B ρ x) (Push.Uniform.block (priced B i p R) 0) J t (height c q T x) (measureK B F t x) y
variable (ht: Trend F A R p u)
include ht
-- B.drape formulas
lemma woodS : ∀ᶠ t in nhdsWithin 0 (Ioi 0),∀ x: Positions (Key B G),yard n t x→∀ y:Positions (Primary c G), let V₁:= postcard G c t y; let w:= postcard G f t (stamp B G x)
    Real.log (measureK B F t y (kerf t x))= -(pushChart B G i (t•meetVar y x)/t^2)+Real.log (F t w):=by
    let fv(t)(u:Y):= B.drape (kerf t u); let g(x):= B.drape (release (1:LinkArray G B.Free) (tape (G:=G) x))
    have hx:g 0=(1:V):=by
        funext i; by_cases hu:i∈B.trunks
        · exact B.on_tree _ ⟨i,hu⟩
        unfold g; rw [show i= (⟨i,hu⟩:B.Free).val from rfl,B.off_tree]; simp [release, show tape (0:Y)= (0:LogArray G B.Free) from rfl] -- rfl is simp?
    have hh : ContinuousAt g 0:=B.continuous_drape.continuousAt.comp (f:=fun z:Y=> release (1:LinkArray G B.Free) (tape (G:=G) z)) ((release_continuous ..).continuousAt.comp (tint G B.Free).continuousAt)
    have hG : Tendsto g (𝓝 (0:Y)) (𝓝 1):=hx ▸ hh.tendsto; obtain ⟨r,hr,hd⟩:= Metric.nhds_basis_ball.eventually_iff.mp (hG.eventually (eventually_all.mpr fun k => Work.F04.prediction_germ hc.branches k i))
    filter_upwards [width,ht.base,(subs n).eventually (eventually_lt_nhds hr)] with t ⟨hz,hB,hf⟩ ⟨he,hq⟩ hH x hs y w; let V':= postcard G c t y; let z:=kerf t x; have h₀(t)(x:Y):t• stamp B G x= stamp B G (t•x):=(map_smul ..).symm
    have h : B.drape z=w:=by
         unfold w postcard;rw [h₀,tango]; unfold z kerf; congr 1; ext1 i; simp only [release, paints,Pi.one_apply,mul_one]
    let u:= t•meetVar y x; have hp : noiseTaylor S V' w i= pushChart B G i u:=by change _= Costree S G i (relayB B G (t • meetVar y x)); rw [map_smul]; unfold Costree; unfold V' w postcard; rw [map_smul, map_smul];rfl
    let W:= fv t x; have hv : t•x∈Metric.ball (0:Y) r:=by rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg hz.le]; exact ((mul_le_mul_of_nonneg_left hs hz.le).trans_lt hH)
    have hw(k:S.Choices): noiseTaylor S V' W k = pushChart B G i u:=by
        rw [← hp]; unfold noiseTaylor; rw [show S.prediction W k= S.prediction W i from hd hv k, show W=w from h]
    let b:=t⁻¹^2; let A:= Real.exp (-b * pushChart B G i u)* F t w
    have hh : measureK B F t y (kerf t x) = A := by
        unfold measureK; rw [pointed (F t) hc he]; calc
            _ = ∑ k,S.likelihood W k*A:=Finset.sum_congr rfl (fun k _=>by unfold A; rw [← hw k,← h])
            _ = _:=by rw [← Finset.sum_mul,S.chosen hc.branches, one_mul]
    -- rename A collision
    rw [hh]; unfold A; rw [Real.log_mul (Real.exp_pos _).ne' (he.pos _|>.ne'), Real.log_exp]; unfold b u; ring
end YM.MSbar.Rolling

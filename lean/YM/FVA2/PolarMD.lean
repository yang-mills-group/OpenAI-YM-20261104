import YM.FVA2.SelfSign
import YM.FVA2.ParityX
/-! # All-components Hart curvature slot parity preserved by ɛ=χ⁻¹.
Any supplied M (even angular freedom) as in Pic. Prove also frame relation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Plot
open Function Filter Set MS MS.Land MS.Landau MS.Logarithm MS.High MS.Tide MS.Menus
open Pert Maxwell Maxwell.Free Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet
open Panel ColorCode Pic Forge Forge.Parity
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
local notation "ℓ"=> V.F
local notation "Θ" => Pic.marked V M s
local notation "Δ"=> par V.F d
local notation "Ω"=> sameAxis V.F d
lemma field_par (i:BasisIx G d) : Δ (Ω i)= (Reed.ϕ (R:=ℂ) i.grade) • Ω i:= physical_inj ℓ ( by rw [par, scalePol_physical,map_smul ]; exact scalePol_pure ℓ PositionX.sign (physicalLabel ℓ d (Ω i)) (graded ℓ i) (m:=(i.size,i.grade)) ) -- cast specify
lemma step (x:Polyp n)(w:Fin n→BasisIx G d) : (Θ).out d x m (Δ ∘ ( Ω ∘ w ))= Parity.segment m • (Θ).out d x m ( Ω ∘ w ):= by
    let F:=Ω ∘ w; let t:= (Θ).out d x m; let c:ℕ:= Reed.rankR ( Fountain.pant w ) Finset.univ; let ϵ:= Reed.ϕ (R:=ℂ); have he: t F=ϵ (c+m)*t F:= by
       obtain hv: (Θ).out d x m F=MS.Dial.tour M ( Fountain.pant w ) s ( Fountain.metric x.1 ) Finset.univ m:= Fountain.onLit V M s w m _; obtain h:= Reed.projection (D:=M) (L:=Fountain.pant w) (s:=s) ( Fountain.metric_conf x.2 ) Finset.univ m; rw [← hv] at h; exact h
    rw [show Δ ∘ (Ω ∘ w)=(fun i=>ϵ (w i).grade • F i) from funext fun i=>field_par V _, MultilinearMap.map_smul_univ, show (∏ i,ϵ (w i).grade)=ϵ c from Finset.prod_pow_eq_pow_sum Finset.univ (fun i=>(w i).grade) (-1:ℂ) ]; change ϵ c • t F= _ • t F; have hv:ϵ (c+m)= ϵ c * ϵ m:=pow_add ..; nth_rw 1 [he]; rw [smul_eq_mul,hv,mul_assoc (ϵ c), ← mul_assoc, show ϵ c * ϵ c=_ from Reed.invol (R:=ℂ) c, one_mul, Complex.real_smul ]; apply congr_arg ( · * _ ); unfold Parity.segment ϵ Reed.ϕ; push_cast; rfl
lemma sign_v : tone Θ:= by
   intro d; apply (Parity.song (d:=d) _ ( clearMark V M s ) ).2; intro i m x p; let f:= (Θ).out d x i; have he : f.compLinearMap (fun _:Fin m=>par ℓ d)= Parity.segment i • f:= by
       apply Module.Basis.ext_multilinear (fun i:Fin m=> sameAxis V.F d); intro t; exact step V M x t
   exact DFunLike.congr_fun he p
include h
abbrev Dfor := nested V.F h (BoxOffice.warehouse V) d
open Verne
lemma χodd (s:ℝ): turn (Elegant.ξ h V M s R)= -(Elegant.ξ h V M s R):= by
    let D:=nested V.F h (BoxOffice.warehouse V); let t:=marked V M s; rw [ ← Pic.realizer ]; exact Bend.meter_odd R (predMarket ( Detector.report (D 6) ( t.lives 6 ) ) ( t.lives 6 )) (Parity.meter (D 6) ( freshMark .. |>.2 6 ) ( sign_v V M _ )) -- sign_v explicit d? predicate def.
lemma inverse_odd (s:ℝ)(P: Pic.pass V h M R) : turn (Forge.transfer V M R s P).f=-(Forge.transfer V M R s P).f:= invert_odd (P.lens s) (χodd V M R s)
-- frame shares sign: use uniqueness. Pick P.η. and transport N. Later.
end YM.FVA2.Plot

import YM.MS.Dial.Slope
/-! Use continuum functions at actual points. independ of support and sampling. Continuity proven at every compact separated shape. Contact output left zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Fleet Puff Engine Actors Puff.Mom
open PeakT -- ordZ
open Vane
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{r:ℕ}[LinearOrder W]{l:Filter I}
variable {B:Deck G}{M:Booked B}(A:MS_Data G M)(u:W→Rake.Label B)
variable [Fintype W] {p:W→ QP}
abbrev Clamp (p d:W→QP): Prop:= ∀ i j:W,i≠j→ ‖p i-p j‖/2<‖d i-d j‖ ∧ ‖d i-d j‖<2*‖p i-p j‖
def Window (w:W)(p d:W→ QP): QP:= open Classical in if Clamp p d then d w else p w
lemma turnH (h:Injective p)(v:ℝ): Mesh ( frameF ( W→QP ) v ) ( fun w=> Window w p ):= by
    intro i j hi; have ht:0<‖p i-p j‖:= norm_pos_iff.mpr ( sub_ne_zero.mpr (h.ne hi) ); have he(d:W→QP): ‖p i-p j‖/2≤ ‖ Window i p d-Window j p d‖∧ ‖ Window i p d-Window j p d‖≤2* ‖p i-p j‖:= by
       unfold Window; split
       next hx=> exact ⟨ ( hx i j hi|>.1 ).le,( hx i j hi|>.2 ).le⟩
       next _ => constructor <;> linarith
    refine ⟨ ⟨ 2*‖p i-p j‖,by positivity, fun t=>?_⟩,⟨ ‖p i-p j‖/2,by positivity,fun t=>?_⟩ ⟩ <;> simp only [roots, frameF,Pi.sub_apply,Pi.zero_apply,exp_zero,mul_one ]; exact (he _).2; exact (he _).1
lemma earlyW (h:Injective p): ∀ᶠ d in 𝓝 p,Clamp p d:= by
    unfold Clamp; apply eventually_all.mpr; intro i; apply eventually_all.mpr; intro j; by_cases hp:i=j; exact Eventually.of_forall fun _ ht=> (ht hp).elim; have ht:0<‖p i-p j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hp)); let U(x:W→QP):= ‖x i-x j‖; have he:= (continuous_apply i|>.sub (continuous_apply (A:=fun _:W=>QP) j)).norm; refine (( show Tendsto U (𝓝 p) _ from he.continuousAt.tendsto ).eventually ( show ∀ᶠ t in 𝓝 (U p), t∈ Set.Ioo ( (U p)/2 ) (2*U p) from isOpen_Ioo.mem_nhds ?_ ) ).mono (fun _ hx _=>hx); constructor <;> unfold U <;> linarith
lemma contin (x:W→QP)(hx:Injective x)(F:Finset W)(s:ℕ) (μ:ℝ) : ContinuousAt (fun x=>tour A u μ x F s) x ∧ ContinuousAt (fun x=>book A u μ x F s) x:= by
    obtain H:= turnH hx μ; have hv : ∀ᶠ y in 𝓝 x, pointI (fun w=>Window w x) y=y:= (earlyW hx).mono fun y hy=> funext fun i=> if_pos hy; obtain h0 := hv.self_of_nhds; have hp(t:W): tend (𝓝 x) x ( Window t x ):= by change Tendsto (Window t x) _ (𝓝 (pointI (fun w=>Window w x) x t)); rw [h0]; apply (continuous_apply t ).continuousAt.tendsto.congr'; exact hv.mono fun i hi=> ( congr_fun hi t ).symm
    obtain ⟨V,hV⟩:= Vane.formal ( builder A H u ); have ht := Rail A u μ H hV x hp F s; have he := Symbol (F:=F) A u μ H hV x hp s; unfold tend at ht he; dsimp only at ht he; rw [h0] at ht he; exact ⟨ ht.congr' (hv.mono fun i hi=> by rw [hi]), he.congr' (hv.mono fun i hi=> by rw [hi]) ⟩
end YM.MS.Dial

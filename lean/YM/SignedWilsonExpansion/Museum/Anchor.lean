import YM.SignedWilsonExpansion.Museum.Genre
/-! # Campaign TRUE labels with contemporaneous Profile & mask bounds all elected periods THEN Cut. Interprets phase later, only fixed labels with Genuine Charge. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SignedWilsonExpansion.Museum
open FullVolume Function Filter Set MeasureTheory Lattice Wilson RG Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open Belle.Path
open PhysicalNext.Repeat.Legato Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale.Level Spec PhysMS PhysMS.Frame
open Next.UVStress Kane.Tilted Scale Rose
open scoped Topology BigOperators Classical ContDiff
variable {ι : Type}{l:Filter ι}{r:ι→ℝ} (p:∀ᶠ i in l,0<r i) {G:Gauge}{n d b:ℕ}{α:Type}
lemma contourFare (φ:Test n) (F H:Points n→ℂ)(U:Set (Points n))(h:tsupport φ⊆U) (C:ℝ) (p:Integrable (fun x=> φ x*F x)) (q:Integrable (fun x=> φ x*H x)) (a:∀ x∈U, ‖F x-H x‖≤ C): ‖φ.applyTo F-φ.applyTo H‖≤ ( ∫ k:Points n,‖φ k‖ )*C:=by
   unfold Test.applyTo; rw [←integral_sub p q]
   have he(u:Points n): ‖φ u*F u-φ u*H u‖≤‖φ u‖*C:=by
      by_cases f:u∈tsupport φ; · rw [←mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (a u (h f)) ( norm_nonneg _ )
      simp [image_eq_zero_of_notMem_tsupport f]
   exact ( norm_integral_le_of_norm_le ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.mul_const C) (Eventually.of_forall he) ).trans_eq (by rw[integral_mul_const])
variable {o:Extraction.Order}(R:Run G){S:Table R.family.book}(F:Final R.family o S){Y:Set (Points n)}
variable (A:Museum.Portfolio S F.room.kernel.spin)(W:ℝ→tower S)(k:(α→ℂ)→ℂ)
variable (u:G.Simple)(O:Roi Y)(Ω:Continuous k)(U:α→ι→Tags G d n)
variable (hv:PositionsUV R.family Extraction.Sequence.full)(hX:(Homes.track o).PointLimits R.family S)
local notation "C" => R.family
local notation "τ₀" => ( fun i x=> k fun a=> PlotW F W none (r i) d n x (U a i) )
local notation "ℳ" => ( fun i a=> costumes R F A W (r i) d ( U a i ) )
local notation "φG" => ( fun i=> cafe C (r i) k (ℳ i) )
local notation "F'" => (Homes.track o)
variable (E:ι→ℝ)(ϵ:∀ᶠ i in l,0 < E i)
include Ω hX u O ϵ p
lemma anchorF : ∀ᶠ i in l, ∀ᶠ v: (ℕ×ℕ) in (F').fuse,(∀ x∈Y, ‖φG i v.1 v.2 x-τ₀ i x‖≤E i ) ∧ (∀ f:Test n,tsupport f⊆ Y→ ‖summit C f (r i) k (ℳ i) v.1 v.2-f.applyTo ( τ₀ i )‖≤( ∫ x:Points n,‖f x‖ )* E i):=by
    filter_upwards [ p,ϵ ] with i hi hε; have H:=orderUniform Y (r i) k O.1 R u F.room.kernel.smooth hX (ℳ i) Ω hi O.2; filter_upwards [Metric.tendstoUniformlyOn_iff.mp H ( E i ) hε] with v hv; let F₀:= τ₀; let H₀:= φG; have hf (x)(hx:x∈ Y):‖H₀ i v.1 v.2 x-F₀ i x‖≤E i:=by
        refine le_of_lt ( lt_of_le_of_lt (le_of_eq ?_) (hv x hx) ); have hx' : F₀ i x=k ( fun a=> S.read ( r i • x ) (ℳ i a) ):= congr_arg k (funext fun a=> (gentry R F A W (r i) ( U a i ) x ( Work.A05.smul_conf hi ( O.2 hx ) )).symm ); rw [hx',dist_comm,dist_eq_norm]
    refine ⟨ hf,fun f hu=>?_ ⟩; rw [← ( Museum.valued C f (r i) k (ℳ i) v.1 v.2 ).1 ]; exact contourFare f _ _ Y hu (E i) ( Museum.valued ..|>.2 ) ( f.smearing ( Ω.comp_continuousOn ( continuousOn_pi.mpr fun i'=> (Plot_neat (F:=F) none hi ( U i' i ) ).continuousOn ) ) ) hf
end YM.SignedWilsonExpansion.Museum

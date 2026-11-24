import YM.LocalLTE.Fan.Medals
/-! Cost Φ high angular in calendar W.v across log sky for trading. No fresh derivative quotas on incoming E! -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Field
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained Gas Ursell FrameBox.Grove
variable {v z r W w s t y η γ B a μ b C C' q X Y : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
variable (H:Cash W t μ L Q o a T R)
variable (K:Captain H j C v z r Y C' w B q m χ)
section
local notation "E"=>Directions G c
variable {p: Directions G c}
lemma haste (U:E→L[ℝ] E)(hU:‖U‖≤ X)(h:Mode FrameBox.Grove.soloV (U p) j a)(hp:a*X≤ s) : Mode (fun x=>FrameBox.Grove.soloV (U x)) p j s:= by
  refine ⟨(le_trans (mul_nonneg h.pos ((norm_nonneg _).trans hU)) hp),fun i=>?_⟩; exact (Brush.reading U (h.atLink i) hU).climb le_rfl hp
set_option maxHeartbeats 200000 in
lemma inflate (Q:E→L[ℝ] E){x:E} {f:Config G c→ℝ} (hF:March.Ore (soloV (Q x)) f z B j) (hz:0<z) (ha:0<a)(hU:‖Q‖≤1)(hp:Mode FrameBox.Grove.soloV (Q x) j a) : Brush j B (z⁻¹*a) ((f ∘ soloV) ∘ Q) x :=by
  let K:ℝ:= z/a; have hK: 0<K:= div_pos hz ha
  let U:=K • Q; let g:= soloV ∘ U; let y:= K⁻¹ • x
  have hv: U y= Q x:= by unfold U y; rw [_root_.smul_apply, map_smul,smul_inv_smul₀ hK.ne']
  have hs:Mode g y j z:=by
     have hp': Mode soloV (U y) j a := by rw [hv]; exact hp
     refine haste U (p:=y) (X:=K) ?_ hp' (?_)
     · unfold U; rw [norm_smul,Real.norm_of_nonneg hK.le]; exact mul_le_of_le_one_right hK.le hU
     unfold K; field_simp; norm_num
  have hθ:g y=soloV (Q x) := congr_arg FrameBox.Grove.soloV hv
  have hΘ:= hF (Directions G c) g y hθ hs
  let D:=K⁻¹ • (ContinuousLinearMap.id ℝ E); have hg: (D x)=y:= rfl; have hh v: U (D v)= Q v:=by
    unfold U; rw [_root_.smul_apply, show D v=K⁻¹ • v from rfl,map_smul, smul_inv_smul₀ hK.ne']
  have he: ((f ∘ soloV) ∘ Q)= (f ∘ g) ∘ D:= by funext i; change f (soloV (Q i))=f (soloV (U (D i))); rw [hh]
  rw [he]; refine (Brush.reading D (x:=x) (g:=f ∘ g) hΘ (e:=K⁻¹) (by unfold D; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hK.le)]; exact mul_le_of_le_one_right (inv_nonneg.mpr hK.le) ContinuousLinearMap.norm_id_le)).climb le_rfl ?_; unfold K; apply le_of_eq; field_simp
lemma fliers (G:Gauge) (j:ℕ): ∃ A:ℝ, 0<A ∧ ∀ (c:Side)(z:Directions G c),‖z‖≤1→ Mode soloV z j A:=by
  obtain ⟨C,hC,H⟩:= Cabana.thick G j; exact ⟨C+1, by linarith,fun _ x he=>later (H _ x he) (le_add_of_nonneg_right zero_le_one)⟩
-- Includes exact Ursell Φ.
include K in
lemma stamina (V:H.fragrances)(x:Directions G c) (Q₁:E→L[ℝ] E)(ha:0<b
    ) (hp:‖Q₁‖≤1)(hs:Mode soloV (Q₁ x) j b)(hf: RG.flags (Pressure.temp t) (soloV (Q₁ x))=∅): Brush j (K.design V) (z⁻¹*b) (fun x:Directions G c=> stream H χ (soloV (Q₁ x)) V) x := by
  have hx: Healthy (Pressure.temp t) (Captain.reachability V) (soloV (Q₁ x)):= by unfold Healthy; rw [hf]; simp
  exact Field.inflate Q₁ (f:=fun U=>stream H χ U V) (K.permitAverage V|>.2.2.2.2 _ hx) K.position ha hp hs -- count?
end
end YM.LocalLTE.Fan.Field

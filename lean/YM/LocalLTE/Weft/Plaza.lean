import YM.LocalLTE.Weft.Cloud
/-! Arp WT and nearby weaker costs for real stencil openings. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Fan Brush Foramen Pastel
variable {v z r W w s t y η γ B a ε α : ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open Weft AnalyticBridge.VerifiedReset FrameBox
variable {X:Grove (c:=c) (0:Site c)} -- edit
local notation "E"=> Directions G c
-- composing paths V_0.Globe.Read.
variable (X0 : Coat T F)
local notation "K" => Disk G c
-- `Plume.δ` near kernel in B_t.A. polynomial in (u^-1) temporary. These costs not used for target estimates, only differentiating evaluator. expose $C/v^K$ per.
structure Weft.Plume {D:Type}[NormedAddCommGroup D][NormedSpace ℝ D] {A:Type}[NormedAddCommGroup A][NormedSpace ℝ A] (k n m:ℕ)(f:ℝ→ D→ A)(C p:ℝ) : Prop where
    jet : Arp k n C f
    scope (s:ℝ):s∈ clip →∀ x, ‖x‖ < p → Brush n (C/s^m) 1 (f s) x
namespace Weft.Plume
variable {D:Type}[NormedAddCommGroup D][NormedSpace ℝ D] {A:Type}[NormedAddCommGroup A][NormedSpace ℝ A]
variable {f:ℝ→D→A} {k k' n m m':ℕ} {C C' p p':ℝ} (h:Weft.Plume k n m f C p)
include h
lemma esteemed (hk:k ≤ k')(hm:m≤ m')(he:C≤C')(hp:p'≤p): Plume k' n m' f C' p':=by
   refine ⟨h.jet.climb hk he,fun s hs x hx=> (h.scope _ hs x (hx.trans_le hp)).climb ((div_le_div₀ (h.jet.nonneg.trans he) he (pow_pos hs.1 _) (pow_le_pow_of_le_one hs.1.le hs.2 hm))) le_rfl⟩ -- edit
omit h
lemma unchanged {f:D→A}{Q k:ℕ}(h₀:p>0)(he:∀ i,‖i‖<p → Brush k C 1 f i): Plume 0 k Q (fun _=>f) C p:=by
   have hh:=he _ (show ‖(0:D)‖<p from norm_zero.trans_lt h₀); refine ⟨Arp.still hh,fun i hi x hx=> (he x hx).climb ((le_div_iff₀ (pow_pos hi.1 _)).mpr (mul_le_of_le_one_right hh.nonneg (pow_le_one₀ hi.1.le hi.2))) le_rfl⟩
lemma fade {f:D→A}{k:ℕ}(h₀:p>0)(h:Weft.Null m k f)(he:∀ i,‖i‖<p→ Brush k C 1 f i):Plume m k m (fun i=> (i^m)⁻¹ • f) C p:=by
   refine ⟨Arp.reduced (h:=he _ (show ‖(0:D)‖<p from norm_zero.trans_lt h₀)) h,fun i hi x hx=> ((he x hx).smul (i^m)⁻¹).climb (le_of_eq ?_) le_rfl⟩
   rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_pos hi.1 _).le),inv_mul_eq_div]
lemma negative (h:Plume k n m f C p) : Plume k n m (fun i=> - f i) C p:=by
   refine ⟨?_,fun i hi x hx=> (h.scope i hi x hx).opposite⟩
   simpa using h.jet.scales (-1)
end Weft.Plume
variable {f₁:ℝ→ Config G f→ℝ}
lemma climbing {κ k' C V:ℝ} (X:Coat T F)(he:P.Funds S T)(q:Site f)(F₀:Grove q)(z:Air f G)(W:BudgetPoint) (h:Scene F₀ κ N j n f₁ C) (hk:Reliable G κ k')(Q:ℕ) (h0:ε>0)(hp:∀ x:K,‖x‖< ε → Brush Q V 1 (F₀.crook N Chi.canonical κ ∘ inputΛ X z) x) (hv:1 ≤ V): Weft.Plume j Q n (fun s=> f₁ s∘ inputΛ X z) (C*Scene.scoreBp n Q V) ε:=by
    refine ⟨Scene.glory Q hk h (show inputΛ X z 0=1 from (by unfold inputΛ; rw [twig0 X he,shaft0])) W (hp _ (norm_zero.trans_lt h0)) hv,fun s hs x hx=>?_⟩
    -- generalize scene.nearby
    exact (Weft.Scene.nearby hs h ((continuous_norm.continuousAt.eventually (gt_mem_nhds hx)).mono fun i hi=>hp i hi) hv).self_of_nhds
end YM.LocalLTE

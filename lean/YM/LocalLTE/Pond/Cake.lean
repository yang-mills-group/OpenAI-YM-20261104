import YM.LocalLTE.Pond.Tactic
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
open Averaging Song Refrain Ovens Payments
variable {M:ℕ} (α Δ:ℝ) (F:ℕ→ EKey n→ Pot G n)
local notation "t₀" => bells p R X M
local notation "t₁"=> azures c p R X g M Δ α F
local notation "E" => Price.tubeX R p X
lemma Comic.scales {n: RegularAddress n}{f} (b:ℝ)(h:Comic G n p f) : Comic G n p (b • f):=by
   refine ⟨CouplingShape.reg_scale b h.1,(by simp [h.2.1]),fun H u v hu hv=>?_⟩
   let F A:= f (increment 1 A)
   unfold logHessian; dsimp only [Pi.smul_apply]; rw [iteratedFDeriv_const_smul_apply' (h.1.smooth 1 (flat_ok ..) |>.of_le (show (↑(2:ℕ):WithTop ℕ∞)≤ (p.order:WithTop ℕ∞) from Nat.cast_le.mpr (by have he:=p.order_ge; omega)))]; change b • (logHessian f u v) = _; rw [h.2.2 H u v hu hv,smul_zero]
lemma rem_rot (s:Signed)(b:Site n) (i:Spikes n) : let t:= (Seat.move s b i.1,i.2); (Price.ridge R p t).support=(Price.ridge R p i).support.image (affine s b) ∧ remises Δ α p R t=remises Δ α p R i ∘ pull s b:=by
    rcases i with ⟨θ,i⟩; intro t; refine ⟨Seat.spread_move ..,funext fun V=>?_⟩; unfold remises; rw [Function.comp_apply]
    let f':= High.fresh R i (0:Site n) (factor*α) (factor*Δ); let f:= f' ∘ θ.view
    let P:=bloomH R p (0:Site n) i; let Q:= High.home R i (0:Site n); change (masked p.threshold ((Seat.move s b θ).spread P) (f' ∘ (Seat.move s b θ).view) - masked p.threshold ((Seat.move s b θ).spread Q) (f' ∘ (Seat.move s b θ).view)) V=(masked p.threshold (θ.spread P) f-masked p.threshold (θ.spread Q) f) _
    unfold f; rw [Seat.distribute,Seat.distribute,Seat.distribute,Seat.distribute, Seat.view_move]; rfl

variable (h:Local X p g a w)(H:∀ j, j ≤ M →∀ i:EKey n, Comic G (Price.tubeX R p X i) p (F j i))
include hR H h hG hd hn
lemma taste (i:Fin (M+2) × EKey n): Comic G (Price.sands p R X M i) p (silt c R X g M Δ α F i):=by
   let j:=i.1.val; unfold Price.silt stairs; split
   next he=> exact (Price.masters hR hG hn hd X g _ _ _ h.smooth).pair (H M le_rfl i.2)
   next hx =>
       split
       next he=> exact H 0 (by omega) _
       next ht=> exact (H i.1 (by omega) i.2).pair (H _ (by omega) _)
lemma deck : Fittings (t₁) t₀ p:=by
   let v:=(silt c R X g M Δ α F); let U:=(t₁); let Y:=(bells p R X M); let e:=numbering (Rol M n); let Z:=sands p R X M
   have he (i:Rol M n): Comic G (Song.revolve Z i) p (Song.choir v i) := Comic.scales _ (Comic.move hG hn (Price.taste hR hG hn hd X g α Δ F h H i.2) i.1 _ rfl rfl)
   let L:=(Collection.fill X R c p g α Δ); let T':=(Local.fittings hG h hR hd hn α Δ)
   let l:=numbering (Fol n); let W:= Sum.elim ((shelves X R p).softer) (fun i:Spikes n=>(Price.ridge R p i).support); let d:=Sum.elim (fill X R c p g α Δ|>.logarithm) (Price.remises Δ α p R)
   have hp (i: Fol n): (∀ q, d i q≠0→ ¬Healthy p.threshold (W i) q)∧Trio.Tidy p (W i) (d i) := by
       rcases i with i|i; exact ⟨T'.visits _,T'.looks _,T'.reads _,T'.steady _⟩
       have hh:= Price.tending Δ α p R hR i; exact ⟨hh.2.1,hh.1⟩ -- edit
   refine ⟨?_,?_,?_,fun i=> (hp (l i)).1,fun i=> (hp (l i)).2.invariant,fun i=> (hp (l i)).2.uses,fun i=> (hp (l i)).2.borel,fun s b=>?_⟩
   · exact ⟨fun i=> (he (e i)).1,fun i=> (he (e i)).2.1,fun i=> (he (e i)).2.2⟩
   · exact ⟨T'.support.sym,T'.support.symtest,T'.support.meas,T'.support.meas_test,T'.support.reads,T'.support.reads_test,T'.support.permit⟩
   · intro s b; obtain ⟨k⟩:= T'.moves s b
     let Z':=Song.whirl (ι:=Fin (M+2) × EKey n) s b; let π:= (e.trans Z').trans e.symm; have ht i:e (π i)=Z' (e i):= Equiv.apply_symm_apply ..
     refine ⟨⟨π,k.kp,?_,?_,k.forced_support,k.forced_inventory,k.forced_tests,?_, k.valuesK⟩⟩
     · intro i; change (Song.revolve Z (e _)).site=_; rw [ht]; exact Song.spirit _ v s b (e i)|>.1
     · intro i; change (Song.revolve Z (e _)).support=_; rw [ht]; exact Song.spirit _ v s b (e i)|>.2.1
     intro i q; change Song.choir v (e _) q=_; rw [ht]; exact congr_fun ((Song.spirit Z _ s b (e i)).2.2) q
   obtain ⟨π,hπ,hY⟩:= T'.carries s b; let v:=Equiv.sumCongr π (Song.whirl (ι:=High) s b); let θ:= (l.trans v).trans l.symm; have hh i:l (θ i)=v (l i):= Equiv.apply_symm_apply ..
   have hz (i:Fol n): W (v i)=(W i).image (affine s b) ∧ d (v i)= d i ∘ pull s b:= by
       rcases i with i|i; exact ⟨hπ _,funext fun U=> hY _ _⟩
       exact Price.rem_rot _ _ _ _ _ -- edit
   refine ⟨θ,fun i=> ?_, fun q i=>?_⟩
   · change W (l _) = _; rw [hh]; exact (hz (l i)).1
   change d (l _) q=_; rw [hh]; exact congr_fun (hz (l i)).2 q
end YM.AnalyticBridge.VerifiedReset.Collection.Price

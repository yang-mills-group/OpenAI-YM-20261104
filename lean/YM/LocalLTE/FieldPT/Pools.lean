import YM.LocalLTE.FieldPT.Ave
/-! Ledger charges for Low and High reset paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {j k z M:ℕ} {W κ K U C V t H: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
section money
variable (j:ℕ) (p:BudgetPoint) (R : PathData G) (c:Clip)(A:Listing G n)(D:Tour A z)(κ:ℝ) (θ:ℝ)(f: ℝ→ℝ) (W:ℝ)
variable {q:ℝ}(h:Reliable G κ q)(hG:G.Simple)(ht:3≤ p.B)(he:32*z<n.val)(hm:2*p.B≤z)(hd:Hex k f)(hp:∀ s∈Weft.clip, |s^2*f s|≤W) (hb:0≤W) {X₁ V₁ :ℝ} {t₁ Λ Λ':ℝ} (hP:R.Bounds c t₁ Λ Λ')(hC:Geo.Width p c t₁)(hg: WilsonStartup.Decent c p)
-- includes Gauge bug.This output ``Comic+DNA'' beyond Ledger.Data original projections.
variable (Ψ:ℝ→ℕ→Pot G n)
set_option quotPrecheck false
local notation "U'"=> (tubeX R p A)
local notation "P'"=> (gallery R p A z D ht)
local notation "K!" s=> Price.vane R c p A z D κ θ (f s) j (Ψ s)
open AnalyticBridge.CouplingShape
include h hG hm hd hp he ht hb
lemma quartets (i:Low)(v:Seat n)(hc:0≤C)(hh:Low.length R i< p.B → Brush (pie j+1) (|i.mark R c| * C) 1 (Low.fresh R c i (0:Site n) factor ∘ soloV) 0) (hg: WilsonStartup.Decent c p) : let g:= Sum.inr (Sum.inl (v,i)); let F:=fun s=> (K! s) g
    DNA (U' g) (P' g) p z (pie j+1) k κ (|i.mark R c| *(W*C)) F ∧ ∀ s∈ Weft.clip, Comic G (U' g) p (F s):= by
    intro g F; let w:= |i.mark R c| *(W*C); have hv n':= Price.payL (R:=R) (κ:=κ) (j:=j) ht hg h hG (0:Site n) (by omega) i n'
    have hy : ∀ s∈Weft.clip,Comic G (U' g) p (F s):= fun s _=> Comic.move hG (by omega) (hv (factor*f s)) v (U' g) (Price.lowLoc ..) rfl
    have hk:0≤ w:=by unfold w; positivity
    refine ⟨⟨hk,?_,?_⟩,hy⟩
    · intro hI s hs; change (gallery R p A z D ht (Sum.inr (Sum.inl (v,i))))=none at hI; unfold gallery at hI; dsimp only at hI; split at hI; cases hI
      next hx=> change Price.swan R c p j κ 0 _ i ∘ _=_; rw [swan,if_neg hx]; rfl
    intro x y hx; change gallery R p A z D ht (Sum.inr (Sum.inl (v,i)))=_ at hx; unfold gallery at hx; dsimp only at hx; split at hx; swap; · cases hx
    next hv =>
       obtain ⟨rfl,rfl⟩:= Sigma.mk.inj (Option.some.inj hx)
       let Q:= i.fresh R c (0:Site n); let X:= (fun s=> Q (factor*f s) ∘ soloV)
       have hu(s:ℝ):X s=f s • (Q factor ∘ soloV):=by funext u; unfold X Q; simp only [Low.fresh, Pi.smul_apply,Function.comp_apply,smul_eq_mul]; ring -- edit
       have ht': Arp k (pie j+1) w X := by
          refine Price.shadings (p:=X) 2 _ (Hex.change (Hex.wallet (m:=k) hd (Hex.constant (k:=0) (Q factor ∘ Grove.soloV))) (fun s hs=> (hu _).symm)) (fun s hs=> Price.shaded hG (x:=⟨(0:Site n),i.home R p 0,i.small_home ..⟩) (i.fresh_regular R c _ hg (factor*f s)) (i.fresh_one R c (0:Site n) _) _) (fun s hs=>?_)
          rw [hu]; exact (((hh hv).smul (f s)).smul (s^2)).climb (le_trans (le_of_eq (show _= |s^2*f s| * (|i.mark R c| * C) from (by simp only [Real.norm_eq_abs,abs_mul]; ring))) ((mul_le_mul_of_nonneg_right (hp _ hs) (mul_nonneg (abs_nonneg _) hc)).trans_eq (by unfold w; ring))) le_rfl
       let V:=Price.sights R p ht (v,i) hv
       let f' s:= Price.swan R c p j κ (0:Site n) (factor*f s) i
       have hF : Weft.Scene V.grove κ V.radius k (pie j+1) f' w:=by
           unfold f' Price.swan; simp_rw [if_pos hv]; exact Scene.spinner _ _ _ _ ht' le_rfl
       exact ⟨by omega, Weft.witnessB V v _ _ _ _ hF h,fun s hs=> hy _ hs|>.1⟩
include hP
lemma treble (i:High)(v:Seat n)(h₀:|θ|≤V)(hc:0≤C)(hh:High.length R i< p.B → Brush (pie j+1) (i.charge R*C) 1 (High.fresh R i (0:Site n) 0 factor ∘ soloV) 0) : let g:= Sum.inr (Sum.inr (v,i)); let F:=fun s=> (K! s) g
    DNA (U' g) (P' g) p z (pie j+1) k κ (i.charge R*((W+V)*C)) F ∧ ∀ s∈ Weft.clip, Comic G (U' g) p (F s):= by
    intro g F; let W':=i.charge R*((W+V)*C); have hz:0 ≤ i.charge R:= Finset.sum_nonneg fun _ _=> abs_nonneg _
    have hΩ:0≤V:=(abs_nonneg _).trans h₀; let E:= U' g; have hZ (s:ℝ)(hs:s∈Weft.clip): Comic G E p (F s):= Comic.move hG (by omega) (Price.payH (j:=j) hP h (0:Site n) i hG (factor*θ) (factor*f s)) v _ (Price.ridgeLoc ..) rfl
    have hΔ:0≤W':=by unfold W'; positivity
    refine ⟨⟨hΔ,?_,?_⟩,hZ⟩
    · intro h' s hs; change (gallery R p A z D ht (Sum.inr (Sum.inr (v,i))))=none at h'; unfold gallery at h'; dsimp only at h'; split at h'; cases h'
      next hx=> change Price.craneH R p j κ (0:Site n) _ _ i ∘ _=_; rw [craneH,if_neg hx]; rfl
    intro x y hx; change gallery R p A z D ht (Sum.inr (Sum.inr (v,i)))=_ at hx; unfold gallery at hx; dsimp only at hx; split at hx; swap; · cases hx
    next hv=>
       obtain ⟨rfl,rfl⟩:= Sigma.mk.inj (Option.some.inj hx)
       let Q:=i.fresh R (0:Site n); let X s:= Q (factor*θ) (factor*f s) ∘ soloV
       have hu(s:ℝ): X s=(θ+f s) • (Q 0 factor ∘ soloV):=by funext u; unfold X Q; simp only [High.fresh,Pi.smul_apply,Function.comp_apply,smul_eq_mul]; ring -- edit
       have ht': Arp k (pie j+1) W' X := by
          refine Price.shadings (p:=X) 2 _ (Hex.change (Hex.wallet ((Hex.constant (k:=k) θ).add hd) (Hex.constant (k:=0) (Q 0 factor ∘ Grove.soloV))) (fun s hs=> (hu _).symm)) (fun s hs=>Price.shaded hG (x:=⟨(0:Site n),High.home R i 0,High.small_home ..⟩) (High.fresh_regular R i (0:Site n) hP p (factor*θ) (factor*f s)) (i.fresh_one ..) _) (fun s hs=>?_)
          have hF: |s^2*(θ+f s)| ≤ W+V:=by rw [mul_add,add_comm]; refine (abs_add_le ..).trans (add_le_add (hp _ hs) ?_); rw [abs_mul, abs_of_nonneg (sq_nonneg _)]; exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hs.1.le hs.2)).trans h₀
          rw [hu, show (fun v=> s^2*((θ+f s) • (Q 0 factor∘soloV)) v) = (s^2*(θ+f s)) • (Q 0 factor∘soloV) from funext (fun _=> (mul_assoc ..).symm)]; exact ((hh hv).smul (s^2*(θ+f s))).climb (le_trans (mul_le_mul_of_nonneg_right hF (hh hv).nonneg) (le_of_eq (by unfold W'; ring))) le_rfl -- edit
       let V:= Price.painting R p ht (v,i) hv; let f' s:= Price.craneH R p j κ (0:Site n) (factor*θ) (factor*f s) i
       have hF : Weft.Scene V.grove κ V.radius k (pie j+1) f' W':=by
          unfold f' Price.craneH; simp_rw [if_pos hv]; exact Scene.spinner _ _ _ _ ht' le_rfl
       exact ⟨hm,Weft.witnessB V v _ _ _ _ hF h,fun s hs=> hZ _ hs|>.1⟩
end money
end YM.AnalyticBridge.VerifiedReset.Collection.Price

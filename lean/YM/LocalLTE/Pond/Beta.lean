import YM.LocalLTE.Pond.Lilac
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
open East Averaging Song Refrain Ovens Payments
-- universal fg per-grade, price restore χ across Calendar y. numerical argument orientation version of rotation anchored. independent p of age.
variable {M:ℕ}(α Δ:ℝ)(F:ℕ→ EKey n→ Pot G n)
local notation "t₀"=> bells p R X M
local notation "t₁"=> azures c p R X g M Δ α F
local notation "g₁"=> Collection.fill X R c p g α Δ
local notation "E" => Price.tubeX R p X
variable {β C₀:ℝ}
def bars (p:BudgetPoint)(M:ℕ)(c b:ℝ) :=turnFee p * ((M+2:ℕ)*(c*b^(chip 0)))
def pocket (n:Side)(M:ℕ)(i:ℕ):ℕ:= (numbering (Price.Rol M n) i).2.1
variable (hxβ:1 ≤ β) (h:∀ i: Fin (M+2), Stocked p (Price.tubeX R p X) (fun k=> Price.silt c R X g M Δ α F (i,k)) (C₀*β^(chip i.val)))
include h hxβ
lemma voracity : let Y:= t₀; let T:= t₁
    ∃ k:ℕ→ℝ,(∀ i,p.supBounds (Y.reg i).site (Y.reg i).support (T.regular i) (k i)) ∧ anchored p Y.reg (fun i=> bloom β (pocket n M i) * k i) (Price.bars p M C₀ β):=by
     intro Y T
     unfold Stocked at h; choose k H hg using h
     let v:= Price.silt c R X g M Δ α F; let b:=Price.sands p R X M; let K:=E; let c:=bars p M C₀ β; let t:=turnFee p; let d:= Song.Rim n; let k' (i: Fin (M+2) × EKey n):= k i.1 i.2; let s (i:Seat n×(Fin (M+2) × EKey n)):=d*(t*k' i.2); let P:=s ∘ numbering (Rol M n)
     have hz:= (turnFee_pos p).le; have ht:=Song.rim_nn n
     have hpβ:0<β:=zero_lt_one.trans_le hxβ; have he (j: Fin (M+2)): bloom β j.val * (C₀*β^(chip j.val))=C₀*β^(chip 0):= by rw [mul_left_comm, East.bloom_price _ _ hpβ, Coup.chip_zero]
     let f i:=bloom β i
     have hr : 0≤ C₀*β^(chip 0):= budget_nonneg (hg 0 (0:Site n)) -- Fin.val 0
     let a:= (M+2:ℕ)*(C₀*β^(chip 0)); have hf:0 ≤ a:=by unfold a; positivity
     let g(i:Fin (M+2) × EKey n):=bloom β i.1.val*k' i
     have hG: anchored p b g a:=by
        intro i; refine Cost.product (f:=fun _ : Fin (M+2)=> C₀ * β^(chip 0)) (by simpa only [a,Fintype.card_fin] using Cost.finite (α:=Fin (M+2)) _ hr) ?_
        intro j; nth_rw 1 [← he j]; exact Quotes.anchored_scale (East.bloom_nn hpβ.le j.val) (hg j) i
     refine ⟨P,fun i=>?_,fun x=>?_⟩
     · let j:=numbering (Rol M n) i; let u:=j.1; let w:=j.2
       change p.supBounds _ _ (Song.Rim n • (v w ∘ (u).view)) (P i)
       have h':=(H w.1 w.2); have hh:= CouplingShape.sup_scale (Song.Rim n) (Song.transSup u h'.1 h'.2); rw [abs_of_nonneg ht] at hh; exact hh -- edit type gap eta
     let F'(i:Rol M n):= d*(t*g i.2); let L:=Song.revolve b
     have hv: anchored p L F' (t*a):= by
        intro x; rw [show t*a=(Fintype.card (Seat n):ℝ)*(d*t*a) by
           have he:= Song.balance n; calc t*a = ((Fintype.card (Seat n):ℝ)* d)*(t*a) := by rw [show _*d=(1:ℝ) from he,one_mul]
                                          _= _:= by ring]; refine Cost.product (Cost.finite _ (show 0≤d*t*a from mul_nonneg (mul_nonneg ht hz) hf)) fun i=>?_
        let y:=StepData.sendSites i.1 i.2
        have hh j:(L (i,j)).site=x ↔ (b j).site=y.symm x:=y.apply_eq_iff_eq_symm_apply
        have hv j: coverNumber p.B (L (i,j)).support=coverNumber p.B (b j).support:= Seat.visit_count ..
        convert Cost.scale (hG (y.symm x)) (d*t) (mul_nonneg ht hz) using 2 with j; dsimp only [F']; simp_rw [BudgetPoint.mass,hh,hv]; split <;> ring
     have hv' i : bloom β (pocket n M i)*P i= F' (numbering (Rol M n) i):= by unfold F' g P s; dsimp only [Price.pocket,Function.comp_apply]; ring
     simp_rw [hv']; exact Cost.equiv (numbering (Rol M n)) (hv x)
-- constructor
lemma rank (he : Price.bars p M C₀ β ≤ a) : ((Price.bells p R X M).pours (Price.azures c p R X g M Δ α F)).EBound p a:= by
     obtain ⟨f,hf,hL⟩:=Price.voracity X g _ _ F hxβ h; refine ⟨f,hf,fun x=>budget_loosen (budget_mono (hL x) (fun i=>?_) ?_) he⟩ -- edit pins order
     · split; next=> exact mul_nonneg (Real.exp_nonneg _) (hf _|>.1)
       exact le_rfl
     intro i; change (if ((Price.bells p R X M).reg i).site =x then _ else _)≤_; split
     next h=> exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hf _|>.1) (East.bloom_bill hxβ _)) (Real.exp_nonneg _)
     exact le_rfl
end YM.AnalyticBridge.VerifiedReset.Collection.Price

import YM.LocalLTE.Pond.Iris
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
section art
open LocalLTE.Cabana in
lemma shave_bill {o:Site n}(X:Grove o) (f g:Config G n→ℝ) (hf:ContDiffAt ℝ (↑j) (f ∘ soloV) 0)(hg:ContDiffAt ℝ (↑j) (g ∘ soloV) 0) : Hall.shave X N κ j (f-g)= Hall.shave X N κ j f-Hall.shave X N κ j g:=by
    let L : Pkt (Directions G n) j →ₗ[ℝ] (Config G n→ℝ):= {
       toFun s:= LocalLTE.FrameBox.realise X N κ (LocalLTE.FrameBox.colorP s)
       map_add' f g:= by
          funext u; unfold LocalLTE.FrameBox.realise; rw [Pi.add_apply]; simp_rw [LocalLTE.FrameBox.sunwheel]; let w:= X.crook N Chi.canonical κ u; have ht (P:Pkt (Directions G n) j): MeasureTheory.Integrable (fun v:G.El=>LocalLTE.Cabana.actual P (LocalLTE.FrameBox.wheel v w)) G.probHaar:= ((LocalLTE.Cabana.moves P ω).continuous.comp (LocalLTE.FrameBox.wheel_moves _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); rw [LocalLTE.Cabana.actual_add]; exact MeasureTheory.integral_add (ht f) (ht g)
       map_smul' c P:=by funext u; unfold LocalLTE.FrameBox.realise; rw [Pi.smul_apply]; simp_rw [LocalLTE.FrameBox.sunwheel]; rw [LocalLTE.Cabana.actual_smul]; exact MeasureTheory.integral_const_mul .. }
    change L _=L _ - L _; rw [← map_sub]; congr; funext i; unfold bushes; simp only [Pi.sub_apply, Tensor.coeff]; rw [show (f-g)∘soloV=f∘soloV-g∘soloV from rfl,iteratedFDeriv_sub_apply (hf.of_le (Nat.cast_le.mpr i.isLt.le)) (hg.of_le (Nat.cast_le.mpr i.isLt.le)),smul_sub]
lemma payoutAt {x:RegularAddress n}(f:Pot G n) : ContDiffAt ℝ j (Residual.payout x f∘soloV) 0:= by
   obtain ⟨C,hp,hC⟩:= Price.vial G j; let t:=∑ i:PlaqAxes,∑ w:PlaqAxes,|projection x f i w|; refine (hC _ _ _ t ?_ _ (by simp)).smooth
   intro i j; apply le_trans (b:=∑ j:PlaqAxes,|projection x f i j|) (Finset.single_le_sum (f:=fun j=>|projection x f i j|) (fun i _=>abs_nonneg _) (Finset.mem_univ j)) (Finset.single_le_sum (f:=fun i=>∑ j:PlaqAxes,|projection x f i j|) ?_ (Finset.mem_univ i)); exact fun _ _=> Finset.sum_nonneg fun _ _=> abs_nonneg _
lemma myth_sub {x:RegularAddress n}(A:Art x d){f g:Pot G n}(h : p.Regular x.support f)(hk:p.Regular x.support g): Price.myth A (f-g) κ j= Price.myth A f κ j - Price.myth A g κ j:= by
   have he:payout x (f-g)=payout x f-payout x g:= by
       have hp:= (label_sub _ _ 0 _ p h hk).1 -- threshold
       unfold rebate at hp; ext v; replace hp:=congr_fun hp v; simp only [Pi.sub_apply] at *; linarith
   unfold myth; rw [he, shave_bill _ _ _ (Price.payoutAt f) (Price.payoutAt g)]; funext i; simp only [Pi.sub_apply,Function.const_apply]; abel
include hd in
lemma swan_mix (R:PathData G)(o: Site n)(i j':ℝ)(b:Low)(κ:ℝ)(j:ℕ) : Price.swan R c p j κ o i b - Price.swan R c p j κ o j' b= Price.swan R c p j κ o (i-j') b:=by
    unfold Price.swan; split
    · have hh := Low.fresh_sub R c b o i j'; exact ((shave_bill (κ:=κ) _ _ _ (Price.lowAt b i _ (pie j+1) p R o hd) (Price.lowAt b j' _ (pie j+1) p R o hd)).symm.trans (congr_arg (Hall.shave (cane o) (p.B-1) κ (pie j+1)) hh))
    exact sub_zero _
lemma spikes_mix (P: BudgetPoint)(R:PathData G)(o:Site n)(α Δ Δ':ℝ)(b:High)(κ:ℝ)(j:ℕ): Price.craneH R P j κ o α Δ b - Price.craneH R P j κ o α Δ' b= Price.craneH R P j κ o 0 (Δ-Δ') b:=by
   unfold craneH; split
   · have hh : High.fresh R b o α Δ-High.fresh R b o α Δ'=High.fresh R b o 0 (Δ-Δ'):= by exact (High.fresh_sub R b o α Δ α Δ').trans (congr_arg (fun k => High.fresh R b o k (Δ-Δ')) (sub_self α))
     exact ((Price.shave_bill _ _ _ (Price.highAt R b o P _ _ _) (Price.highAt R b o P _ _ _)).symm.trans (congr_arg (Hall.shave (cane o) P.B κ (pie j+1)) hh))
   exact sub_zero _
lemma hail_bill {f w:ℕ→ Pot G n} (h:∀ i,p.Regular (X.reg i|>.support) (f i))(hk:∀ i,p.Regular (X.reg i|>.support) (w i))(i:ℕ) : hail X d V f κ j i - hail X d V w κ j i= hail X d V (f-w) κ j i := by
    unfold hail; cases hl: V i
    · simp -- edit
    next A=> exact (Price.myth_sub A (h i) (hk i)).symm
lemma sw_mixH (p:BudgetPoint)(R:PathData G)(α Δ Δ':ℝ)(i:Spikes n):
    Price.craneH R p j κ (0:Site n) (factor*α) (factor*Δ) i.2 ∘ i.1.view-Price.craneH R p j κ (0:Site n) (factor*α) (factor*Δ') i.2 ∘ i.1.view = Price.craneH R p j κ (0:Site n) (factor*0) (factor*(Δ-Δ')) i.2 ∘ i.1.view:=by
    rw [mul_zero,mul_sub]; funext v; exact congr_fun (Price.spikes_mix p R 0 _ _ _ _ _ _) (i.1.view v)
include hd in
lemma sw_mixL (R:PathData G)(Δ Δ':ℝ)(i:Faces n): Price.swan R c p j κ (0:Site n) (factor*Δ) i.2 ∘ i.1.view-Price.swan R c p j κ (0:Site n) (factor*Δ') i.2 ∘ i.1.view= Price.swan R c p j κ (0:Site n) (factor*(Δ-Δ')) i.2 ∘ i.1.view:=by
    rw [mul_sub]; funext v; exact congr_fun (Price.swan_mix hd R 0 _ _ _ _ _) (i.1.view v)
include hd in
lemma vane_bill {f w:ℕ→ Pot G n} (h:∀ i,p.Regular (X.reg i|>.support) (f i))(hk:∀ i,p.Regular (X.reg i|>.support) (w i))(α Δ Δ':ℝ) :
   vane R c p X d V κ α Δ j f-vane R c p X d V κ α Δ' j w=vane R c p X d V κ 0 (Δ-Δ') j (f-w):=by
   funext i; cases i with
   | inl i=> exact Price.hail_bill X V h hk i
   | inr i=>
      cases i with
      | inl i=> exact Price.sw_mixL hd R Δ Δ' i
      | inr i=> exact Price.sw_mixH p R α Δ Δ' i
end art
end YM.AnalyticBridge.VerifiedReset.Collection.Price

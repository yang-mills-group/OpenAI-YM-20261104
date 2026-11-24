import YM.LocalLTE.Pond.Cake
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
variable {M:ℕ}(α Δ:ℝ)(F:ℕ→ EKey n→ Pot G n)
local notation "t₀"=> bells p R X M
local notation "t₁"=> azures c p R X g M Δ α F
local notation "g₁"=> Collection.fill X R c p g α Δ
local notation "E" => Price.tubeX R p X
-- Gift cumulative. budgets per grade finite survived sym.tune requests. Exact.
variable (h: Local X p g a w)
variable (hΔ:p.threshold^2* |Δ| ≤ a)
include hR hΔ hG h hd hv hn
lemma bonded (U:Config G n) (H:(t₀|>.pours t₁).EBound p u): ((t₀).pours t₁).additive p U=((shelves X R p).pours g₁).additive p U +∑' i: Spikes n, Price.remises Δ α p R i U:=by
    obtain ⟨t,-,ht,hx⟩:= Price.lake hR hv hG hn hd X g Δ α h hΔ U
    obtain ⟨j,hj,hJ⟩:=H; let e:=numbering (Rol M n); let f:= Price.silt c R X g M Δ α F
    let P:= Price.tubeX R p X; let Z:= Price.sands p R X M; let J:= Price.azures c p R X g M Δ α F; let L:= Price.bells p R X M; let f':=shadeA p (Song.revolve Z) (Song.choir f) U
    have hz:Summable f':= by
       have hs:Summable j := by
         let A:=L.pours J; let T (x:Site n) i:= if (A.reg i).site=x then p.mass (A.reg i).support (j i) else 0
         exact (summable_sum (s:=Finset.univ) (fun i _=> (show Summable (T i) from (hJ i).2.1))).of_nonneg_of_le (fun i=>(hj i).1) (fun i=> by simpa [T] using p.loMass (A.reg i).support (j i) (hj i).1)
       apply (Equiv.summable_iff e).1; exact hs.of_norm_bounded (fun i=> CouplingShape.mask_cost (hj i) U)
    change (∑' i, f' (e i)) =_; rw [←ht,e.tsum_eq, hz.tsum_prod,tsum_fintype]
    have hK (s:Seat n)(i:EKey n)(j : Fin (M+2)) : f' (s,(j,i))= Song.Rim n* shadeA p P (stairs M (archive X R c g α Δ) F j.val) (s.view U) i:= Song.tune ..
    have hp (s:Seat n) : (∑' j:Fin (M+2)× EKey n,f' (s,j))= Song.Rim n * t:= by
       let Q:=Equiv.prodComm (EKey n) (Fin (M+2))
       let b j:=f' (s,j); have ht : Summable (fun k=> b (Q k)) := (Equiv.summable_iff Q).2 (hz.comp_injective (Prod.mk_right_injective s))
       rw [← Q.tsum_eq b, ht.tsum_prod]; apply Eq.trans (b:= ∑' i:EKey n,∑ j:Fin (M+2), b (Q (i,j))) (tsum_congr fun i=> tsum_fintype _) (?_)
       have h i : ∑ j:Fin (M+2), b (Q (i,j))=Song.Rim n*shadeA p P (archive X R c g α Δ) (s.view U) i:=by -- edit
          unfold b; change ∑ j:Fin (M+2), f' (s,j,i)=_
          simp_rw [hK]; rw [← Finset.mul_sum]; apply congr_arg; exact Price.rounded ..
       simp_rw [h]; rw [tsum_mul_left]; exact congr_arg _ (hx s|>.tsum_eq)
    simp_rw [hp]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,Song.balance,one_mul]
omit hn in
lemma righteous (U:Config G n) : Summable (fun i:ℕ=> (g₁).logarithm i U):=by
    obtain ⟨s',hs',ht'⟩:= h.cheap; have he:=Collection.Local.quote_family hR hd hv α Δ hs' ht' hΔ; let l:= numbering (LKey n)
    let k' i:=Collection.quoteL R p c α Δ s' (l i); let Y:= shelves X R p
    have hk (i:ℕ)(U:Config G n): ‖(g₁).logarithm i U‖≤ k' i:= Local.quote_soft hG α Δ hs' h.smooth (l i) U
    have hV : Summable k':= RG.Activities.summable_charge Y.sites (fun i=>(norm_nonneg _).trans (hk i 1)) (drop_reserve _ _ (fun i=>(norm_nonneg _).trans (hk i 1)) (fun i=> Cost.equiv l (he.2 i))) -- edit
    exact hV.of_norm_bounded (fun i=> hk i U)
lemma monks (β v:ℝ)(U:Config G n) (H:(t₀|>.pours t₁).EBound p u) : (trunk R c p (t₀) (t₁) β v).eval U*Real.exp (∑' i,(t₁).logarithm i U)=(trunk R c p (shelves X R p) (fill X R c p g α Δ) β v).eval U*Real.exp (∑' i,(g₁).logarithm i U):=by
   obtain ⟨-,hy,-⟩:= Price.lake hR hv hG hn hd X g Δ α h hΔ U
   let y:= ∑' i: Spikes n, Price.remises Δ α p R i U
   let A:=(g₁); let Y:=(t₁); let L:=numbering (Fol n)
   have hp : ∑' i,(Y).logarithm i U=(∑' i,A.logarithm i U)+y:= by
      let f:Fol n→ℝ:=Sum.elim (fun i=>A.logarithm i U) (fun i=> Price.remises Δ α p R i U)
      have hdy(i:ℕ): (Y).logarithm i U=f (L i):=by change (Sum.elim _ (Price.remises Δ α p R) (L i) : Config G n→ℝ) U=_; cases L i <;> rfl
      simp_rw [hdy, L.tsum_eq f]; exact Summable.tsum_sum (f:=f) (Price.righteous hR hv hG hd X g α Δ h hΔ U) hy -- binder hv
   let X':=(shelves X R p).pours A; let Z:=(t₀).pours Y
   have hz : Z.additive p U=X'.additive p U+y:= Price.bonded hR hv hG hn hd X g α Δ F h hΔ _ H
   have ht : Z.gas p U=X'.gas p U:= rfl
   let x':= v*(Fintype.card (Site n):ℝ) - (R.inChannels c p β U)
   unfold Progress.DirectedRecipe.trunk RG.Rep.eval RG.Rep.exponent; dsimp only
   change Real.exp (x'-Z.additive p U)*Z.gas p U*Real.exp (∑' i,Y.logarithm i U)=Real.exp (x'-X'.additive p U)*X'.gas p U*Real.exp (∑' i,A.logarithm i U)
   rw [ht,hp,hz,mul_right_comm _ (X'.gas p U),mul_right_comm (Real.exp _) (X'.gas p U) (Real.exp (∑' i,A.logarithm i U)),←Real.exp_add,←Real.exp_add]; ring_nf
end YM.AnalyticBridge.VerifiedReset.Collection.Price

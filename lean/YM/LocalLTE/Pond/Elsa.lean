import YM.LocalLTE.Pond.Coins
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
-- total symmetry.SUM independent.H.Use propagation with E expression. Identities, clocks.Y∆. Use only for actual v values.
open Song Refrain Ovens Payments BetaTransport
variable {ι:Type}
def shadeA (p: BudgetPoint) (A:ι→RegularAddress n)(f:ι → Config G n→ℝ)(V:Config G n)(i:ι):= masked p.threshold (A i).support (f i) V
lemma Stocked.arcs {A:ι→RegularAddress n}{f:ι → Config G n→ℝ}(h:Stocked p A f k)(V:Config G n) : Summable (shadeA p A f V) := by
    obtain ⟨v,h,hP⟩:=h
    let f' (o: Site n) i:=if (A i).site=o then p.mass (A i).support (v i) else 0
    refine Summable.of_norm_bounded (summable_sum (s:=Finset.univ) (fun i _=> (show Summable (f' i) from (hP i).2.1))) fun i=>?_
    exact (CouplingShape.mask_cost (h _ |>.2) _).trans (by simpa [f'] using p.loMass (A i).support (v i) (h _|>.2.1))
variable (Δ α:ℝ)
lemma rays (U:Config G n)(i:Spikes n) : shadeA p (Price.tubeX R p X) (archive X R c g α Δ) U (Sum.inr (Sum.inr i)) = shadeA p (incoming X R p) (archive X R c g α Δ) U (Sum.inr (Sum.inr i)) + remises Δ α p R i U:=by
    unfold shadeA remises; rw [Pi.sub_apply]; change masked _ (Price.ridge R p i).support (freshly Δ α R i) U = masked _ (highEntry G R i).support (freshly Δ α R i) U + (_-_); abel
-- Anchorage old probability Summable.
include hG hR hd hv hn
variable (h:Local X p g a w)(hp:p.threshold^2*|Δ| ≤ a)
include h hp
local notation "X₀"=> shelves X R p
local notation "V₀"=> fill X R c p g α Δ
local notation "K" => archive X R c g α Δ
local notation "Z"=> Price.tubeX R p X
lemma lake (U:Config G n): ∃ t:ℝ, Summable (fun i:Spikes n=>Price.remises Δ α p R i U) ∧ t= ((shelves X R p).pours (fill X R c p g α Δ)).additive p U+ ∑' i:Spikes n,Price.remises Δ α p R i U ∧ ∀ u:Seat n, HasSum (shadeA p (Price.tubeX R p X) (archive X R c g α Δ) (u.view U)) t:=by
    obtain ⟨v,hu,hP⟩:= h.cheap; let H: Meadow.Budget p X.reg g.logRead a:= ⟨v,hP,fun i=>⟨h.smooth i,hu i⟩⟩
    let f:= V₀; let y:=X₀; let F:= K; let z:=Z
    have hG':Stocked p z F _ := Price.dock hR hv hG hn hd X g α Δ H hp
    have h': Stocked p (incoming X R p) F (regularNeed G p c σ C' α a):= by
       have he i:= Local.quote_regular hG hR hd α Δ hu h.smooth i
       refine ⟨quoteE R p c α Δ v,fun i=>⟨?_,he i⟩,(Local.quote_family hR hd hv α Δ hu hP hp).1⟩
       let A:=(X₀).pours (V₀); let e:=numbering (EKey n); have hz:= h.regFamily hG hR hd hn α Δ |>.smooth (e.symm i); change p.Regular (incoming X R p (e _) |>.support) (archive X R c g α Δ (e _)) at hz; rwa [Equiv.apply_symm_apply] at hz
    let r (i:Spikes n):= Price.remises Δ α p R i
    have hz (U:Config G n) : Summable fun i:Spikes n=> r i U:=by
       let M: Spikes n→ EKey n:=fun i=> .inr (.inr i); have he:Injective M:= Sum.inr_injective.comp Sum.inr_injective
       let g':=shadeA p z F U; let f':= shadeA p (incoming X R p) F U
       have hp (i:Spikes n): r i U=g' (M i)-f' (M i):= by rw [show g' (M i)=_ from Price.rays X g Δ α U i];change r i U=f' (M i)+r i U-f' _; ring -- edit
       simp_rw [hp]; exact ((hG'.arcs U).comp_injective he).sub ((h'.arcs U).comp_injective he)
    have hu (i:Spikes n)(s:Signed)(b:Site n) (V:Config G n): let t:= (Seat.move s b i.1,i.2); r t V=r i (pull s b V) :=by
       rcases i with ⟨θ,i⟩; intro t; unfold r Price.remises
       let f':= High.fresh R i (0:Site n) (factor*α) (factor*Δ); let f:= f' ∘ θ.view
       let P:=bloomH R p (0:Site n) i; let Q:= High.home R i (0:Site n); change (masked p.threshold ((Seat.move s b θ).spread P) (f' ∘ (Seat.move s b θ).view) - masked p.threshold ((Seat.move s b θ).spread Q) (f' ∘ (Seat.move s b θ).view)) V=(masked p.threshold (θ.spread P) f-masked p.threshold (θ.spread Q) f) _
       unfold f; rw [Seat.distribute,Seat.distribute,Seat.distribute,Seat.distribute, Seat.view_move]; rfl
    let c₀:= ((shelves X R p).pours (fill X R c p g α Δ)).additive p U
    let c':= c₀ + ∑' i:Spikes n,Price.remises Δ α p R i U; refine ⟨c',hz _,rfl,fun θ=>?_⟩
    let v:= θ.view U; let L:= shadeA p (incoming X R p) F v; let s':= θ.1; let b':= θ.2
    have hL:= h'.arcs v
    have hk: Summable fun i:Spikes n=> r i v:= hz v
    have ht : ∑' i,L i = c₀:= by
       let N:=(X₀).pours (V₀); have ht:=((Local.fittings hG h hR hd hn α Δ).moves s' b'|>.some) -- edit
       rw [← (numbering _).tsum_eq L]; exact Marlin.streams p U ⟨N.E,N.K⟩ 0 s' b' ⟨N.reg,N.forced⟩ ht
    let g'(i:EKey n):= Sum.elim (fun _=> (0:ℝ)) (Sum.elim (fun _=>0) (fun i=> r i v)) i
    have hB : HasSum g' (0+ (0+∑' i: Spikes n, r i v)):= HasSum.sum (show HasSum (fun _:ℕ=> (0:ℝ)) 0 from hasSum_zero) (HasSum.sum (f:= Sum.elim (fun _:Faces n=> (0:ℝ)) (fun i=> r i v)) hasSum_zero hk.hasSum)
    simp only [zero_add] at hB
    let e : Equiv.Perm (Spikes n) := Song.whirl s' b'; have he : ∀ i:Spikes n,r i v = r (e i) U:= fun i=> (hu i s' b' U).symm
    have hx : (∑' i: Spikes n,r i v) = ∑' i:Spikes n,Price.remises Δ α p R i U:= by simp_rw [he]; exact e.tsum_eq (fun i=> Price.remises Δ α p R i U)
    rw [hx] at hB; rw [show shadeA p (Price.tubeX R p X) K (θ.view U) = L+g' from ?_]; swap
    · funext i; rcases i with i|i|i
      · exact (add_zero (L (Sum.inl i))).symm
      · exact (add_zero (L (Sum.inr (Sum.inl i)))).symm
      exact Price.rays X g Δ α v i
    have hh: HasSum L c₀ := ht ▸ hL.hasSum; exact hh.add hB
end YM.AnalyticBridge.VerifiedReset.Collection.Price

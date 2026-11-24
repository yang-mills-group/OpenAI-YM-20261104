import YM.RGComparison.Core16.Lam.Rank
/-!
# Uniform Hess gauge and readback on primitive seam

Proof doesn't require Θ field order prices when paying iteration at this block vs a history's future calls. Enter tickets via `Stencil` only then earn `Aspiration` script. Projection earnings include paying *two* extra orders of base
before transferring into probing loss. All internal moments normalized by the same pot and only canceled in that estimator on that specific term.
Build uses orientation arbitrary positive K, not a new Temp law by design.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk Stage
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {P: Patch} {K:KernelChoices} {d:f.val=c.val*P.L.val} {I L:Type}[Fintype I][Fintype L]
    {W:Oven P}{X:Shelf G (PlaqAxes⊕Axis) W.Xways}

variable (hS:P.Branches K G) (hW: Parcel.Oven.Offers W X K) (B:Forest (StepData.mk P K d).ratio) (H: Bid.Larger (G:=G) (StepData.mk P K d))
local notation "S"=> StepData.mk P K d
local notation "G0"=> gear S B X
include hW

lemma fluorescence (A:Lumen.Stage)(r N:ℕ){u:ℝ}(hu:0 ≤ u) (ψ:I→ (L→G.Color)→ℝ)(he:∀ i,ContDiffAt ℝ ω (ψ i) 0) :∃ (U:Lumen.Stage)(c:ℝ), U.Above A ∧ 0≤c ∧ Visit U X ∧ ∀ {c' f': Side}{d : f'.val=c'.val*P.L.val} (T:Forest (StepData.mk P K d).ratio), Bid.Larger («S»:=StepData.mk P K d) (G:=G)→ ∀ (F: News G c'→ℝ)(i p),ContDiff ℝ ∞ F→ Visible X (ψ i) (scoop (StepData.mk P K d) T F) p N u→ pursed U (stamps (gear _ T X) p (ψ i)) (fun g=> port (StepData.mk P K d) T g F) r c:=by
    obtain ⟨C,z,hC,hc,hT,h⟩:= Lumen.vintage hW.good A ψ (fun i=>(he i).of_le le_top) (r+1) 0 0 N hu; obtain ⟨U,hU,hE⟩:= Fk.date_purchase C
    refine ⟨U,2*z,Lumen.above_trans hC hU,by positivity,newer hc hU,fun {c f d} T h' F i p hf hv=>?_⟩
    let R:= StepData.mk P K d; let V:=gear R T X; let HH:= paint R T hW h'; let Z x:= port R T x F 
    have hx:= h T.Free (Hut.Rooms c f) (R.Choices) _ _ _ f V HH _ _ _ hv (fun i hi=> by omega) [] (Nat.zero_le _)
    rw [Fk.translate] at hx
    apply (presents T hW h' (ψ i) hv (he i) hf).money hU hE (hx.reload ?_); intro x hx
    dsimp only [Fk.baron,Function.comp_apply]; rw [pow_zero,one_mul]; exact (turned_bill R T hW h' hf (hc x hx)).2.symm

-- Receipt, r P pressure. ∀-price before period. Norms ℝ. Body reading post-context at RESIDUAL foot support: not in gauge Gram mark price yet; retain independent ALL local order uses semantics.
def Fares (W:Oven P)(X:Shelf G (PlaqAxes⊕Axis) W.Xways)(K:KernelChoices)(r:ℕ)(U:Lumen.Stage)(z:ℝ):Prop:=∀ (c f:Side)(d:f.val=c.val*P.L.val),
    let R: StepData c f:=⟨P,K,d⟩
    Bid.Larger (G:=G) R→ ∀ (T: Forest R.ratio)(i j:Operand G c), pursed U (pokes W X T i j) (polls R i j) r z
include hS

lemma marquee (A:Lumen.Stage)(r:ℕ):∃ (U:Lumen.Stage)(v:ℝ), U.Above A ∧ Visit U X ∧ 0≤v ∧ Fares W X K r U v:=by
    obtain ⟨L,hL⟩:= seals G K; have hp : 0 < L:= hL.floor
    obtain ⟨V,y,hV,hy,hE,hv⟩:=fluorescence (X:=X) hW A r (b0 X) hp.le (heatΨ W K) (yearly hS _)
    let q:=r+2
    obtain ⟨U,x,hU,hx,hQ,Hq⟩:= fluorescence hW V q (b0 X) hp.le (tileΨ W K (G:=G)) (fun i=>(daily hS W i).1)
    obtain ⟨T,c',hT,hc,h,H⟩:= fluorescence hW U q (2*b0 X) (pow_nonneg hp.le 2) (hearth W K (G:=G)) (fun i=>(hourly hS W i).1)
    let z:= pursed.forecastCost q x x; have hz:0≤z:=by unfold z pursed.forecastCost; positivity
    refine ⟨T,y+(c'+z),Lumen.above_trans hV (Lumen.above_trans hU hT),h,by positivity,?_⟩
    intro c f d Λ hs B i j
    let p:= raise Λ (compass i); let x':= raise Λ (compass j); let u (F:News G c→ℝ) (g:ℝ):= port Λ B g F
    let A:= u (p*x')-u p* u x'; let V' := u (tip Λ (compass i) (compass j))
    have he(b:Operand G c) : pursed T (bud W X B b) (u (raise Λ (compass b))) q x:= pursed.widen (Hq B hs _ (profileDatum b) _ (raise_hot (StepData.mk P K d) _) (visor hW B hs hL b)) hT rfl
    have hA: pursed T (osier W X B i j) A q (c'+z):= pursed.difference (H B hs (p*x') (profileDatum i,profileDatum j) _ (show ContDiff ℝ ∞ (p*x') from (raise_hot Λ _).mul (raise_hot Λ _)) (fusion hW B hs hL i j)) (pursed.product (he i) (he j)) -- hx rewrite Tier. Λ let
    have hVa:pursed T (smooth W X B i j) V' r y:= pursed.widen (hv B hs _ (tier i j) _ (tip_hot Λ ..) (hued hW B hs hL i j)) (Lumen.above_trans hU hT) rfl
    exact (pursed.renew (pursed.difference hVa (pursed.roll_up hA (valenced B hW hs i j))) (fun x hx=> (Lam.measure_point Λ B hs.1 (dollar_pos x).ne' (compass i) (compass j)).symm))
end YM.RGComparison.Core16.Lam

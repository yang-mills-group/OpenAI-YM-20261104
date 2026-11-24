import YM.LocalLTE.Quartz.Tapes
import YM.LocalLTE.MarkPT.Dish
/-! Orbit-shared explicit mark proposal. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
-- parity.Y allele tall cone factor.Deferred.B.Gouge.
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')
variable (Φ:ℕ→ℝ→ Config G f→ℝ)(Ψ:ι→ℝ→ Config G f→ℝ)
open Weft
noncomputable def pinPT (i:H.ThinP) (u:Tickets (sign M S))(m:ℕ)(s:ℝ)(p:Disk G c):= likely fun r:Greenbelt.Reserve S=> likely fun k:S.Choices=>
    Fan.wishPT (L:=L) (o:=o) (t:=t) M Q u ((Greenbelt.prism T t χ o.K (1:Config G c) (Greenbelt.allot r)).taggedL k) (Captain.quietR M i u) (Fan.fibers H i) m Φ Ψ s p
noncomputable def micaPT (m:ℕ)(s:ℝ)(x:Disk G c):=∏ i:Option (Fin z.fst),pinPT M H χ Φ Ψ (z.2 i) (D i) m s x
noncomputable def twirlPT (m k:ℕ)(F:Directions G c→L[ℝ] Directions G c) (s:ℝ)(x:Directions G c): ℝ:= Field.speedΛ H z.2 *LocalLTE.stem k (Fan.micaPT M H χ z D Φ Ψ m s) (s,F x)
noncomputable def lensPT (m k h:ℕ){u:Site c}(X:Grove u)(κ:ℝ)(hp:2*(2*h)≤ c.val)(s:ℝ):Config G c→ℝ:=FrameBox.realise X h κ (FrameBox.colorP (fun i:Fin k => Tensor.coeff (Fan.twirlPT M H χ z D Φ Ψ m k (Fold.trace u h hp) s) i 0)) -- Fold need additional imports
local notation "v₀'"=> Ux
local notation "I'"=> Option (Fin z.fst)
variable (u:Veil c f→ℝ) (hu:∀ i,0 ≤ u i)
variable (C)
variable (hC:1≤ C)(m:ℕ) (h:∀ i:Option (Fin z.fst),∀ (F:Forest S.ratio)(X:Coat T F), X.x=t→X.width=o.K→ Warp J j (((team M (D i)).weight*∏ j∈quietR M (z.snd i) (D i),u j)*C) (fun s=> Fan.wishPT (L:=L) (o:=o) (t:=t) M Q (D i) X (quietR M (z.2 i) (D i)) (fibers H (z.2 i)) m Φ Ψ s))
def clockQ (q j:ℕ)(C:ℝ) := C^(q+1)*(1+(↑(q+1:ℕ):ℝ))^j
local notation "C₀"=> canvasX M H z D u
include hx hu h hC
lemma phaser : Warp (J*(q+1)) j (C₀*clockQ q j C) (fun s=> Fan.micaPT M H χ z D Φ Ψ m s):=by
    letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    let Y(i:I'):= pinPT M H χ Φ Ψ (z.2 i) (D i) m; have hv i:Warp _ _ _ (Y i):= East.organZ (fun s (x: Disk G c)(F:Reserve S)=> _ ) (fun F=> East.organZ _ fun k=> h i _ ((Greenbelt.prism T t χ o.K (1:Config G c) (Greenbelt.allot F)).taggedL k) rfl rfl) -- edit infer K X ?
    have hf:= Warp.ballads univ (fun i _=> hv i); rw [card_univ,Fintype.card_option,Fintype.card_fin,prod_mul_distrib,prod_const,card_univ,Fintype.card_option,Fintype.card_fin] at hf
    have hl: z.fst+1 ≤ q+1:=Nat.succ_le_succ hx.can.length; refine hf.grow (Nat.mul_le_mul_left _ hl) (?_); unfold canvasX clockQ; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun i _=> mul_nonneg (Team.profit _) (prod_nonneg fun i _=> hu i)); gcongr
lemma twinkles (F:Directions G c →L[ℝ] Directions G c)(hf:‖F‖≤1) (hm:k≤j) (ε:ℕ) :
    Arp (J*(q+1)+k) ε ((|Field.speedΛ H z.snd| * C₀)* ( (k:ℝ) *(clockQ q j C)*(2:ℝ)^k*(1+(k:ℝ))^ε)) (fun s=> Fan.twirlPT M H χ z D Φ Ψ m k F s):=by
    let f:=(0:Directions G c→L[ℝ]ℝ).prod F; let Q: Disk G c:=(1,0); have hq: ‖Q‖≤1:=max_le (by simp : ‖(1:ℝ)‖≤1) (show ‖(0:Directions G c)‖ ≤ 1 from by rw [norm_zero]; linarith)
    have hg : ‖f‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound f zero_le_one (fun i=> by rw [one_mul]; exact max_le (show ‖(0:ℝ)‖≤‖i‖ from by simp) ((F.le_opNorm i).trans (mul_le_of_le_one_left (norm_nonneg _) hf)))
    have hv:= Warp.stencil Q hq hg ε (phaser M H χ z D C q n r₀ A' hx Φ Ψ u hu hC m h) hm
    refine ((hv.scales (Field.speedΛ H z.2)).climb le_rfl (le_of_eq (by ring))).adjust (fun i hi=> funext fun v=>?_)
    exact congr_arg (fun z₀=> Field.speedΛ H z.2 * stem k (micaPT M H χ z D Φ Ψ m i) z₀) (show i • Q+ f v=(i,F v) from (by unfold Q f; simp))
end YM.LocalLTE.Fan

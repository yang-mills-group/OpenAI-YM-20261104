import YM.LocalLTE.MarkPT.Patch
import YM.LocalLTE.Vinyl.Prospects
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
open East FrameBox
-- Same LΩ calls. head P.Trace.First. No assumption on moment as $function of u$: primitives. Any potential.Cap.P
def cheerM (m q p k j:ℕ) := (max 2 k*q*p+m*p)*(p+1) + j
-- outer CT; m takes J.K.N
lemma anthem {P:Teller G}(Q:ConnectedActivityE6.Target G P)(W:ℝ)(o: Target.Order G W)(L:Side)(D:Patch)(hd:D.Branches P.bind G) {u a:ℝ→ℝ}(hu:Rate G L 0 u)(ha:Rate G L 0 a) (K k J n p p' q m:ℕ){κ q':ℝ}(hk:Reliable G κ q') (hG:G.Simple) : ∃ M:ℝ→ℝ, Rate G L 0 M∧∀ᶠ x in atTop,0≤ u x→0 ≤ M x∧∀ (c f:Side)(S: StepData c f)(T:Tube G S), S.patch=D→ ∀ (R:Rep G f)(μ σ:ℝ)(H: Cash W x μ L Q o σ T R)(r:ℕ→ℕ)(Φ:ℕ→ℝ→ Config G f→ℝ)(φ:ℕ→ℝ), (∀ y,SumBudget (fun i=> if (R.activities.reg i).site=y then φ i else 0) 1)→ (∀ i,r i≤ p' → CanX κ (L.val*radiusB x) K k (Φ i) (R.activities.reg i).site (φ i*u x))→∀ (ι:Type)(N':ι→Lotus.Leaf R)(Ψ:ι→ℝ→ Config G f→ℝ)(P':ι→Prop),(∀ i,P' i → Caption (N' i) κ (L.val*radiusB x) J n (Ψ i) (a x))→ ∀ (χ:Chi)(z:Stars H N'), Candor N' z.1 z.2 p p' r P'→ let C:=|Field.speedΛ H z.1.snd| * canvasX N' H z.1 z.2 (Fan.ratioCash R (East.jewel P L x) φ); let l:= East.stagnate p Q.halo* radiusB x; ∀ (X:Grove (Fan.origin N' H z))(hs:2*(2*l)≤ c.val),
    Scene X κ l (Fan.cheerM J q p K m) m (fun s=> Fan.lensPT N' H χ z.1 z.2 Φ Ψ q m l X κ hs s) (C*M x):=by
   let j:=m+1
   let M (x:ℝ):= (East.pubFee L G Q.halo p (radiusB x)); have hM:Rate G L 0 M:=by exact (show Rate G L 0 (fun x=> (ballCost (stagnate p Q.halo * radiusB x):ℝ)) by simpa using! Census.width_rate G L (East.stagnate p Q.halo) 0).mul_right _
   let N x:=L.val*radiusB x; have hN:Rate G L 0 (fun x=>(N x:ℝ)):=by unfold N; push_cast; exact Rate.radius_price.mul_left _
   obtain ⟨V,hV,H⟩:= latticeMark Q W o L D hd (East.jeweled P L) hu ha Rate.radius_price hN hM hk hG j K k J n p q (Nat.succ_pos m)
   let U' x:ℝ:= (m:ℝ)*Fan.clockQ p j (V x)*(2:ℝ)^m*(1+(m:ℝ))^m
   have he: Rate G L 0 U':= by
       have hv':Rate G L 0 fun x=> clockQ p j (V x):= (((hV.pow (p+1)).weaken (by simp)).mul_right _)
       exact (((hv'.mul_left (m:ℝ)).mul_right ((2:ℝ)^m)).mul_right ((1+(m:ℝ))^m))
   refine ⟨(fun x=> |U' x|), Brim.absolut he,?_⟩; filter_upwards [H] with x hV hg; have ht:= hV (East.jewels P L x) hg
   refine ⟨abs_nonneg _,?_⟩; intro c f S T hS R μ σ H r Φ φ hU he ι N' Ψ T₀ hy χ z hv C l X hs
   let P':= (fun u=>Fan.ratioCash (c:=c) R (East.jewel P L x) φ u); have hp₀:= East.highwayQ H φ hU; have hC:0 ≤ C:= mul_nonneg (abs_nonneg _) (prod_nonneg fun i _=> mul_nonneg (Team.profit _) (prod_nonneg fun i _=> (hp₀.1 i).1))
   let f:= Fold.trace (Fan.origin N' H z) l hs (G:=G); have hf:‖f‖≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by rw [one_mul]; exact Fold.invoice ..
   let κ':= max 2 K*q*p+J*p
   have hψ:= Fan.twinkles N' H χ z.1 z.2 _ p p' m r T₀ hv Φ Ψ P' (j:=j) (fun i=> (hp₀.1 _).1) ht.1 q (J:=κ') (?_) f hf (by unfold j; omega) m
   · exact (Weft.Scene.spinner m X m l hψ le_rfl).generous _ le_rfl (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
   intro i F X h hh; let S₀:= (z.2 i); let A:= quietR N' (z.1.snd i) S₀
   have he' := Fan.weaving N' H z.1 z.2 p p' r T₀ hv i
   have ht' (j) (hj:j∈ A) : labelGrade (c:=c) R κ Φ φ (N x) (radiusB x) K k (u x) j:=by -- inference
       rcases j with j|j
       · exact he j (hv.loans j i hj)
       have h:=(hv.can.each i).stretch j (he'.1 hj); rcases j with j|j|j|j <;>first|exact h|trivial
   have hd: fibers H (z.1.snd i)= Field.pin (East.docket H z.1 i) H:=by unfold Field.pin Fan.fibers; rw [← (hv.can.each i).lift]
   exact ht.2 _ _ S T hS R μ σ H F X h hh φ Φ A ((card_le_card he'.1).trans (hv.can.each i|>.received)) _ (by rw [show Fan.fibers H _= _ from hd]; exact East.caps H z.1 hv.can i) (fun i _=> hp₀.1 i) ht' ι N' Ψ S₀ he'.2.1 (fun j hj=> hy j (hv.petals i j hj))
end YM.LocalLTE.Fan

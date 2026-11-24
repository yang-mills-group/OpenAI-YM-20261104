import YM.RGLocalTaylor.Laminate.Under
import YM.RGLocalTaylor.Laminate.Exhale
import YM.MergeProof.Shaded
import YM.MergeProof.Hens

/-!
# Analytic full log supply for the post-frame real mark sector

Reads and prices in native representation (polynomial `Sound` after `ways`,
headSheet unbundled list supported LOG marks incl singletons, all sectors). K
reservation from motion at its actual eligibility. Exports both before tallies
& after for field use. Do not drop or move the post-reset Fest evaluation
partners or assume compaction has analytic derivatives across the seam!
Quantities enter Model & Bare at LABELS; remain prior to any compression.
K prices use tariff at full exponent incl +1. Division en route from `lauge` to
Taylor power is paid separately. No positivity of signed measures used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March Captain
namespace Laminate
open RG01.Survive Trees Merge Palette Gas Ursell Marker GridApprox.Nil
open MergeProof MergeProof.Accent AnalyticBridge VerifiedReset Collection Quotes Next.Foundations Height
open Extra.Trajectories
variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (N : Captain H j C' d v Y A b r B q n χ)
    {τ:Type} [Fintype τ][DecidableEq τ] {Cen : Marker.Census τ}(o': τ→Site c) (p:BudgetPoint) (y:ι→Poly Cen) (cost:τ→ℝ)

-- qualifications for *any* such scanner inside the reads; Aperiodic χ not limited here.
structure Month (H : Cash W s μ L Q o C T R): Prop where
   theta j : (y j).part Cen.quiet=0
   rotor i : y i*y i=0
   coverage i : Push.GridApprox.Nil.Scoped (A:={j:τ|o' j∈(M' i).crest.image S.ratio.parent}) (y i)
   graph : Plot M' H rA
   cash i : 0<cost i
   ticket i : Marker.Poly.price cost (y i) ≤ 1

open Merge.Photo Motion Switch Ovens
variable {RR:Rep G c} (K' : ℝ→Finset ι → Code G c)
set_option quotPrecheck false
local notation "O" => Chi.canonical
variable (H) (R' : RG.Rep G c)
-- consumption support, ALL letters regardless of kernel positivity
abbrev renter (χ:Chi) (keep:H.fragrances→ℕ→Prop) (M:ℕ) (u:H.fragrances):= masked (Pressure.temp s) (Reach H u) (stained M' rA y u (χ:=χ) keep M)

def playsOut (χ:Chi) (tail:H.fragrances→ℕ→Prop) (M:ℕ) (U:Config G c): Marker.Poly Cen :=let R:= R'; (↑(Real.exp (R.exponent U)):ℂ) • (Poly.pass (∑' i, (renter H M' rA y χ (fun i k=>¬tail i k) M i U+renter H M' rA y χ tail M i U))*∑' m,Photo.fronts R.activities (fun i=>Fleece K' Cen y i U) U R.p m)

/-- quantitative post-producer for the `Photo` contract, thereafter feeding
Permit/Towed/Given. Prices on regular germ BEFORE masking (supports nonempty,
even all permission costs and gauge). Preserve full f (Taylor output) not just
nonzero approximation. `K` not re-expanded here: keep every `Fleece` with its
registration and extra masks. Membership G-wave aft(U) forces critical payment
here; compatible with post-Rep.Activities and gas before sector summation.
-/
structure SignedPage (χ:Chi) (M:ℕ) (ρ w:ℝ) : Prop where
    old : ∃ d e,Usable M' H χ R' rA K' d e w
    exp' T p : (∀ i k, T i k → p ≤ k) → Swing o' R'.p cost (Reach H) (fun z=> stained M' rA y z (χ:=χ) T M) (R'.p.supportExponent+1) ((ρ^p)⁻¹)
    ticketwise T i : headSheet M' H χ rA Cen y i=renter H M' rA y χ (fun i k=>¬T i k) M i + renter H M' rA y χ T M i
    all : Towed cost (fun i=>(R'.activities.forced i).support) (Photo.Fleece K' Cen y) R'.p.B (R'.p.supportExponent+1) w
    permit i V : Photo.Fleece K' Cen y i V≠0→ (R'.activities.forced i).eligible R'.p.threshold V
    license i : Flow o' (barcode R'.activities i) (Photo.Fleece K' Cen y i) R'.p.threshold
    holds T : (S.push R.beta (Photo.given (S:=S) M' rA Cen y))=playsOut H M' rA y K' R' χ T M

variable {M : ℕ} {θ K ρ a b' α uJ e vJ η w β δ ε : ℝ} {M' H R' K' rA cost o' y N}
namespace SignedPage

lemma selfieAt {ρ w:ℝ} (h: SignedPage H M' rA o' y cost K' R' χ M ρ w)
    (hm:Month M' rA o' y cost H) (U : Config G c) (q:ℕ) : (Fleece K' Cen y q U).part Cen.quiet=↑(R'.activities.K q U):=by
   obtain ⟨a,b,h⟩:=h.old; obtain ⟨v,hp,hM⟩:=h.gas.bought; let g U t p:= K' t p q U; rw [Fleece, sunset g (hp q) y U hm.theta]; unfold g; rw [h.gas.term]

variable (hT:Month M' rA o' y cost H) (hh:Photo.Usable M' H O R' rA K' a b w) (hv:∃ P':BudgetPoint,P'.B=R'.p.B ∧ Motion.Pays R'.activities P' K' w (R'.p.supportExponent+1))
include hT hh hv
set_option maxHeartbeats 500000 in
lemma supplied (h: Laminate.Known H ε b' 1 η R'.p.order R'.p.power M) (he : R'.p.B=radiusB s)
    (hε : R'.p.supportExponent+1 ≤ ε) (ht: 0<η) : SignedPage H M' rA o' y cost K' R' O M (Mayer.arcRadius G L s) w:= by
   have ha:= (add_pos R'.p.exponent_pos zero_lt_one).le; have hB:= hh.temp
   obtain ⟨A,a',C,d,v',t,r',B,q',e,K,θ,uJ,vJ,k,l,N,hG,hP,hF,hW,hL⟩:=h; obtain ⟨J,hK,hV⟩:= hv
   let hH:=Palette.Plot M' H rA; let ρ := Mayer.arcRadius G L s
   have hh' (V:Config G c) T i :Photo.headSheet M' H O rA Cen y i V =renter H M' rA y O (fun i k=>¬T i k) M i V+renter H M' rA y O T M i V:=by
      rw [landing M' rA N y hT.rotor hT.theta i V hT.graph T M]; unfold renter; by_cases hx:Healthy (Pressure.temp s) (Reach H i) V
      · simp only [masked_eq _ _ _ _ hx]; unfold Reach at hx; simp only [masked_eq _ _ _ _ hx, Pi.add_apply]
      rw [masked_ne _ _ _ _ hx, masked_ne _ _ _ _ hx]; unfold Reach at hx; rw [masked_ne _ _ _ _ hx,add_zero]
   constructor
   · exact ⟨a,b,hh⟩
   · intro tail p hp; let g':= Airs.gP (l:=l) (M:=M) (e:=e) (uJ:=uJ) (θ:=θ) (ρ:=ρ) (α:=(M+4:ℝ)*r'+vJ) M' rA N
     let u' := Airs.aP (l:=l) (M:=M) (e:=e) (uJ:=uJ) (θ:=θ) (ρ:=ρ) (α:=(M+4:ℝ)*r'+vJ) M' rA N
     have h₀: Axle M' rA M R'.p.order H v' O u' g' ρ:= hW.grants M' rA N hT.graph
     have hY:Sailor G R'.p.threshold q' R'.p.order:= by rw [hB]; exact ⟨fun c g hb=> N.weigh.stroke c g (hb.trans N.talent)⟩
     apply Swing.larger (ahead R'.p tail hT.theta hT.cash hT.ticket hT.coverage h₀ hB le_rfl le_rfl he N.income hY N.near N.position (show Trees.Ready H.smallAt R'.p.B (fun i=>2^R'.p.order*g' i) _ _ _ _ from he.symm ▸ (hW.pricebook M' rA hT.graph)) hp (ha.trans hε) hε ht)
     have hv :0<ρ:= lt_of_lt_of_le zero_lt_one hW.scale; exact mul_le_of_le_one_right (inv_nonneg.mpr (pow_nonneg hv.le _)) (by simpa only [one_mul] using hL)
   · exact fun T i=>funext fun V=> hh' V T i
   · rw [← hK]; exact Photo.flag_K _ _ Cen y cost hT.cash hT.ticket hV ha
   · intro i V h; exact freight (u:=fun U t j=> K' t j i U) V (fun m hx=>(hh.gas.rear i m).2.2.2 V hx) h
   · exact Photo.river M' H O R' rA K' Cen y hh o' hT.coverage
   intro T; funext V; rw [← Photo.acts M' H O R' rA K' _ y hT.rotor hh hT.theta]; unfold playsOut
   refine congr_arg _ (congr_arg (fun i: Marker.Poly Cen=> Poly.pass i* _) (tsum_congr ?_)); intro i; exact hh' V T i
omit hh hv
variable (h:SignedPage H M' rA o' y cost K' R' χ M ρ w)
include h
-- Dense compaction at the SAME analytic price (Burns+Towed after compaction, p.Regular deriv support on individual labels before compaction). No claim about application of Season, reanchoring or packing error that may not preserve price.
local notation "b's" => R'.p.supportExponent+1
lemma paint {tail:H.fragrances→ℕ→Prop} (hh:∀ i k,tail i k→ l≤ k) : Towed cost (Reach H) (renter H M' rA y χ tail M) R'.p.B (R'.p.supportExponent+1) ((ρ^l)⁻¹) :=by
    have ht: ∀ tail, renter H M' rA y χ tail M=fun i=> masked R'.p.threshold (Reach H i) (stained M' rA y i tail (χ:=χ) M):=by
      intro T; obtain ⟨_,_,hh⟩:=h.old; unfold renter; rw [hh.temp]
    rw [ht]; exact (h.exp' _ _ hh).fleet hT.cash ((add_pos R'.p.exponent_pos zero_lt_one).le)
omit hT in
lemma burns (tail:H.fragrances→ℕ→Prop) (i:H.fragrances) : Burns o' (Reach H i) (renter H M' rA y χ tail M i) R'.p.threshold:=by
   have h' := h.exp' tail 0 (fun _ _ _=>Nat.zero_le _)|>.burn i; obtain ⟨a,b,H⟩:=h.old; rw [H.temp] at *; exact h'
end SignedPage
end Laminate
end YM.RGLocalTaylor

import YM.RGLocalTaylor.Laminate.Portrait
/-!
# SAME post-readout witnesses can go here. `SignedPage` enters actual
`Canopy` after compression while retaining the labelled prices. Use the
analytic estimate on the labels before desired further smooth transformations;
tally potentially sacrifices regular off-mask extension (no assertion of
summability for tally of all unmasked fields). We DO furnish Towed support
prices after compression, in the indicated full-height regular/forced channels
with all singleton/force predicates accounted for. This is the SAME K posting
and offshell dose reaching Canopy, not identifying a separate witness.

Proofs of canonical price & support adapted from Appl, Shade, Tally. 
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
open MergeProof Accent AnalyticBridge VerifiedReset Collection Quotes Next.Foundations
variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (N : Captain H j C' d v Y A b r B q n χ)
    {τ:Type} [Fintype τ][DecidableEq τ] {Cen : Marker.Census τ}(o': τ→Site c) (p:BudgetPoint) (y:ι→Poly Cen) (cost:τ→ℝ) (z:H.fragrances)
open Merge.Photo Motion Switch Ovens Extra.Trajectories
variable (K' : ℝ→Finset ι → Code G c)(R' : Rep G c) {M l₁ : ℕ} {ρ w:ℝ}
namespace SignedPage
variable {M' rA K' o' R' y cost} (hT:Month M' rA o' y cost H) (h:SignedPage H M' rA o' y cost K' R' χ M ρ w)
variable (keep:H.fragrances→ℕ→ Prop)
def tallyTag (H : Cash W s μ L Q o C T R) (M':ι→Leaf R) (y:ι→Poly Cen) (rA:ι→ℝ) (keep:H.fragrances→ℕ→ Prop) (χ:Chi)(M:ℕ):= tally (Reach H) (renter H M' rA y χ keep M)

set_option quotPrecheck false
local notation "wT" => R'.p.supportExponent+1
local notation "hi" => tallyTag H M' y rA
-- includes Health at use. Need check preserving h.skin Cold.B'
include hT h
lemma spinPull (Y:Support c)(U:Config G c): spine M' H χ rA Cen y Y U= hi (fun i n=>¬keep i n) χ M Y U +hi keep χ M Y U := by
    let a T u:= renter H M' rA y χ T M u U; have ht (T): Summable (fun i:{i // Reach H i=Y}=>a T i.val):= by apply ((Towed.repair (h.paint hT (tail:=T) (fun i k _=> Nat.zero_le k)) hT.cash U).2).comp_injective Subtype.val_injective
    change ∑' i:{i//Reach H i=Y}, headSheet M' H χ rA Cen y i.val U=_
    simp_rw [h.ticketwise keep, Pi.add_apply]; exact Summable.tsum_add (ht _) (ht _)
lemma compressed (hh:∀ i k,keep i k→ l₁≤ k): Towed cost id (hi keep χ M) R'.p.B wT ((ρ^l₁)⁻¹) ∧∀ i,Burns o' i (hi keep χ M i) R'.p.threshold:= by
    have he := h.paint hT hh; haveI : Countable H.fragrances:= by unfold Cash.fragrances Clusters Cash.ThinP; infer_instance
    exact ⟨towing _ _ (show Towed cost (id ∘ Reach H) _ _ _ _ from he) hT.cash,transitE _ (r:=id) (fun i=> h.burns keep i) (fun V=> (he.repair hT.cash V).2)⟩
lemma coverB : Towed cost id (spine M' H χ rA Cen y) R'.p.B wT 1:=by
    let T: H.fragrances→ℕ→Prop:= fun _ _=>True; have he:= h.compressed hT T (fun _ i _=>Nat.zero_le i); rw [pow_zero, inv_one] at he
    rw [show spine M' H χ rA Cen y= hi T χ M from ?_]; exact he.1
    funext i V; rw [spinPull hT h T i V, show hi (fun i n=>¬ T i n) _ _ i V=0 from ?_,zero_add]
    unfold tallyTag Accent.tally; refine Eq.trans (tsum_congr fun i=>?_) tsum_zero; unfold renter masked stained passenger; simp [T]
lemma forcedTravel : Towed cost Prod.fst (Photo.chain R' K' Cen y) R'.p.B wT w:= towing _ _ (show Towed cost (Prod.fst ∘ barcode R'.activities) _ _ _ _ from h.all) hT.cash

open Menu
variable (q : ι→Menu.Hat Cen R)(D:GaugeDoor R R')
variable (hf:∀ i,M' i=(q i).M)(ht:∀ i, rA i= sumFee (q i) cost)(hp:∀ i,y i=Menu.sing (q i) cost)
    (he:SoundDoor S D) (hz:∀ U i j, Switch.jet (fun t s=> K' t s i U) {j}=sumFee (q j) cost* D.hinge (q j).M i U)
local notation "K0" => chain R' K' Cen y
local notation "Y" => spine M' H χ rA Cen y
include hf ht hp he hz
structure Publishes (q:ι→ Menu.Hat Cen R)(D:GaugeDoor R R') (o':τ→Site c)(cost:τ→ℝ) (e k w z:ℝ)
    (U : Support c → Config G c→Poly Cen)(V:Box c→ Config G c→Poly Cen)(S : StepData c f): Prop where
    enact : S.push R.beta (Expense q cost S)=play R' Cen V (fun x=>∑ i,U i x)
    earnest : Towed cost id U R'.p.B e k
    burns : ∀ i,Burns o' i (U i) R'.p.threshold
    fair : Towed cost Prod.fst V R'.p.B w z
    floods : ∀ i,Flow o' i (V i) R'.p.threshold
    selfie : ∀ x i,(V i x).part Cen.quiet=profile R'.activities (fun j=>Complex.ofReal ∘ R'.activities.K j) i x
    sing : ∀ i x v,(V i x).part (Cen.fire v)=∑ j,owl (q j) D v i x
omit h hT hf ht hp he hz in
lemma Publishes.canopy {q:ι→ Menu.Hat Cen R}{D:GaugeDoor R R'}{o':τ→Site c}{e k w z:ℝ}{U:Support c→ Config G c→Poly Cen}{V:Box c→ Config G c→Poly Cen}{S:StepData c f}(h:Publishes q D o' cost e k w z U V S) : Canopy S D o' cost e w k z q:= ⟨_,_,h.earnest,h.burns,h.fair,h.floods,h.enact,(fun i U=>h.selfie U i),h.sing⟩
lemma canopyTape : Publishes q D o' cost wT 1 wT w Y K0 S:= by
   have hV:= hT.cash
   obtain ⟨a,b,hr⟩:= h.old
   have ht' :=Photo.scored M' H χ R' rA K' _ y hT.rotor hr cost hT.cash hT.ticket hT.theta
   refine ⟨?_,h.coverB hT,Photo.serenade _ H χ _ _ _ _ _ hr _ hT.coverage _ hV hT.ticket hT.theta,h.forcedTravel hT,Photo.heavily _ H χ _ _ _ _ _ hr _ hT.coverage _ hV hT.ticket,Photo.selfie _ H χ _ _ _ _ _ hr _ hV hT.ticket hT.theta,fun i U j=>?_⟩
   · have hv : Expense q cost S= Photo.given M' rA Cen y (S:=S):= by rw [funext hf,funext ht,funext hp]; rfl
     rw [hv]; exact funext ht'
   let k:ℕ→Poly Cen:=fun t=> Fleece K' Cen y t U; let l(t) (p:ι):ℂ:= (↑(D.hinge (q p).M t U):ℂ)*(Menu.stamp (q p)).part (Cen.fire j)
   have hx(t): (k t).part (Cen.fire j)=∑ i,l t i:=by
      unfold k Fleece; rw [Accent.quality (fun U t' p=>K' t' p t U)]; refine sum_congr rfl fun i _=>?_ ; rw [hz]; unfold l; rw [hp,← Menu.purchase _ hV,Poly.part_smul,Complex.ofReal_mul]; ring
      exact hT.theta
   have hh(i'):Summable (fun t=> l t i'):=by
       obtain ⟨v,hR⟩:=he.volume
       obtain ⟨c,h,hB⟩:=hR (q i'|>.M)
       exact ((h.2.1.of_norm_bounded («f»:=fun i=> (↑(D.hinge (q i'|>.M) i U):ℂ)) fun t=> ((hB t).2 _).trans (R'.p.loMass _ _ (hB t).1))).mul_right _
   change (∑' t:{t // barcode R'.activities t=i},k t.val).part (Cen.fire j)=_
   rw [Poly.share];
   · simp_rw [hx]; rw [Summable.tsum_finsetSum]; apply sum_congr rfl; intro p _; unfold l Menu.stamp owl; simp_rw [tsum_mul_right,Poly.part_send]; split_ifs with hp hQ he
     · rw [mul_comm];rfl
     · exact False.elim (hQ hp.symm)
     · exact False.elim (hp he.symm)
     · rw [mul_zero]
     intro p _; exact (hh p).comp_injective Subtype.val_injective
   exact ((h.all).repair hT.cash U).2.comp_injective Subtype.val_injective
end SignedPage
end Laminate
end YM.RGLocalTaylor

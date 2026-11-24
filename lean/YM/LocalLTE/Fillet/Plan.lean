import YM.LocalLTE.Ballot.Pulse
import YM.LocalLTE.ScaleX.Height
import YM.LocalLTE.Ballot.Ear
import YM.LocalLTE.Quartz.Mint
import YM.LocalLTE.Quartz.Ops
import YM.LocalLTE.Quartz.Allot
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
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
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove

/-! ## Isolated marked analytical program

Rank discipline for repeated canonical steps needs a **strict power gain
without increasing angular rank** on a marked packet. Keep only the
isolated singleton molecule; pay every leg of the remainder. The coefficient
is nontrivial: includes weighting by the *same* auxiliary quadratic lens. -/

open Daisy Daisy.Charity
private lemma oneCoefficient (s:H.ThinP): coefficient H.seam (chip H s).snd=1 := by
    unfold coefficient
    let v : Option (Fin 0) → H.ThinP:=fun _=>s
    have he : pot H.seam v=∅:= by
      apply Finset.eq_empty_iff_forall_notMem.mpr; intro p hp; have h:= (potential_mem H.seam v p |>.mp hp).1
      have hv : p.card ≤ 1:= (Finset.card_le_univ _).trans (by simp); omega
    change Graph.mass (pot H.seam v)=1; rw [he]; unfold Graph.mass; have hh : Graph.reaches (∅: Graph.Network (Option (Fin 0))) := by
      intro i j; rw [Subsingleton.elim i j]
    have he : Graph.connectedGroups (∅:Graph.Network (Option (Fin 0)))={∅}:= by ext i; simp only [Graph.belongs,Finset.subset_empty,Finset.mem_singleton]; exact ⟨And.left,fun e=> e.symm ▸ ⟨rfl,hh⟩⟩
    rw [he]; simp [Graph.alternating]
lemma oneSpeed {s:H.ThinP} : Field.speedΛ H (chip H s).snd=1:=by unfold Field.speedΛ; rw [oneCoefficient]; simp [Charity.chip]

variable {M} (i:ι)(N:H.ThinP)(h:prince (M i) H (chip H N))
local notation "ί"=> (chip H N)
local notation "φ'"=> (gateP M i (chip H N) none)

private lemma chip_s (j:Option (Fin (chip H N).fst)): j=none:=Subsingleton.elim (α:=Option (Fin 0)) _ _
include h
lemma oneReach (j:Option (Fin (chip H N).fst)): (φ' j).reach = N.val:=by
   have hK := chip_s H N j -- order
   subst j; have hk: N.val={(M i).turn.badge S}:=h.2.1; rw [hk]; unfold gateP; rw [if_pos rfl]; change Finset.image _ ({i}:Finset ι)=_; rw [image_singleton]
lemma oneQuiet (j:Option (Fin (chip H N).fst)): Captain.quietR M N (φ' j)=∅:=by unfold Captain.quietR; rw [oneReach H i N h]; unfold East.lining; simp
lemma onePrice (z: Veil c f→ℝ): canvasX M H (ί) (φ') z=(M i).weight:=by
    let f j:= (team M (φ' j)).weight*(∏ l∈ quietR M N (φ' j), z l); change ∏ j,f j=_; rw [Finset.prod_eq_single (none:Option (Fin (chip H N).fst))]; swap; · intro b hb hf;exact (hf (chip_s H N b)).elim
    swap; · simp
    unfold f; rw [oneQuiet H i _ h,prod_empty,mul_one,Palette.worth, gateP,if_pos rfl]; exact Finset.prod_singleton ..
variable (hM:∀ j,(M i).turn= Wing.logKey j→(R.activities.reg j).support ⊆ Animals.neighbors (S.patch.L.val*radiusB t) (R.activities.reg j).site)
lemma oneOrchestra (he: 1≤q) (hj:∃ j,(M i).turn=Wing.logKey j) (hM:∀ j,(M i).turn= Wing.logKey j→(R.activities.reg j).support⊆ Animals.neighbors (S.patch.L.val*radiusB t) (R.activities.reg j).site) : Candor M (ί) (φ') q n r₀ (· = i) :=by
   obtain ⟨j,hj⟩:=hj; let z: Veil c f:= .inl j; let B:=radiusB t
   have hz: N.val={(M i).turn.badge S}:= h.2.1
   have hZ: N.val={elastic (S:=S) z}:= by rw [hz,hj]; rfl
   have hp k:East.docket H (ί) k={z}:=by
      let Z:= East.lining S N.val
      ext i; change (i∈Z) ↔ i∈{z}
      have h:i ∈ Z ↔ elastic i∈N.val:= Finset.mem_preimage; rw [h,hZ]; simp [Fan.runOut.eq_iff]
   have hP : Ac.Spark H.supportP N.val:=by
       rw [hz]; refine ⟨Finset.singleton_nonempty _,fun a ha b hb=>?_⟩; have he:a=b:=(Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm; subst b; exact .refl
   refine ⟨⟨Nat.zero_le _,fun i=>?_, ?_,(oneCoefficient H N).trans_ne one_ne_zero⟩,fun k=> ?_, fun k j hj=>?_ ,fun j k hk=>?_⟩
   · refine ⟨hP,h.2.2, ?_, ?_,?_,?_⟩
     · rw [hp]; exact hZ.trans (Finset.image_singleton ..).symm
     · rw [hp,Finset.card_singleton];exact he
     · rw [hp]; simp [z]
     rw [hp]; intro j' hj'; have hk:j'=j:= Sum.inl.inj (mem_singleton.mp hj'); subst j'; exact hM j hj
   · refine ⟨none,j,?_⟩; change elastic z ∈ N.val; exact hZ.symm ▸ Finset.mem_singleton_self _
   · exact subset_of_eq (oneReach H i N h k)
   · have h: k=none:= chip_s H N _; unfold gateP at hj; rw [if_pos h] at hj; exact mem_singleton.mp hj
   have hh :False:=by change _ ∈ quietR M N _ at hk; rw [oneQuiet H i N h] at hk; exact Finset.notMem_empty _ hk
   exact hh.elim
omit h
lemma oneTerm : Charity.matin (M i) H (ί) χ= wingTerm (χ:=χ) (ί) M (φ'):=by
    rw [Captain.speaksP M i (ί)]; rw [Finset.sum_eq_single (none:Option (Fin (ί).1))]; exact if_pos (Captain.tag_yes M i (ί) none); intro j _ h; exact (h (chip_s H N _)).elim; simp
end YM.LocalLTE.Fan

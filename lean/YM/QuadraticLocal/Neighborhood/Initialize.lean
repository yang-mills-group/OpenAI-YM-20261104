import YM.QuadraticLocal.Neighborhood.Theory
import YM.QuadraticLocal.Deletion.Crop
/-!
# Large-load boot on a single actual receipt. Supply at ANY R.Attn.Parent.Card.

Unmasked source coefficients `F:T→Gram`; `Lamps.nominal` already powerful
 and can encompass cylinders of arbitrary shape meeting the specified bounds.
 We render the **complete actual density with these AMS**, using ALL
 forced labels chosen jointly with the real vacuum representation. Payment
 from additional Willow couple.Path.V.Science`. NOT requesting any thinning
 via coupling cost per mark at the itinerary. Relative to Θ even at startup!
 Choose a boost at all nonempty source occurrences and use stronger-inflated
 K costs available BEFORE merger. Handles any simultaneous Mark polynomial
 on any number adapted to the census. Output root.M Ω bills then use it.
 Include full-group norm in addition to regular Theta root input.Sensor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Neighborhood.Origin
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local Extra.Multi
open Throng Canopy
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {Pa : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {T : Type*}{I:Type} {w : V → ℝ} {a α β γ k b r t :ℝ} {B : ℕ}
variable {P: Rep G n}
variable (hw: ∀ i,0<w i)
variable (L:Lamps T I G P.p o R) -- on the announced stage! canonical Display.
set_option quotPrecheck false
local notation "p"=> P.p
local notation "ζ"=> P.activities
local notation "X"=> (P.p.supportExponent)
local notation "Q"=> (P.p.Support)
variable [Countable I][Fintype V]

def whole (t:T)(i:I)(U:Config G n): Poly R:= Poly.send (L.mode i) (L.nominal t i U)
abbrev enabled (i:I)(U:Config G n):= L.clear i ∨ Healthy P.p.threshold (L.ground i) U
def bill (t:T)(i:I)(U:Config G n): Poly R:= if enabled L i U then 0 else whole L t i U
-- follows previous proof `Spill`. Adapt to non-Row.No assumption on coupling.
def shifts : ShiftRows T I G P.p o R where
  place i:= ⟨L.ground i, ⟨_,(L.address i).anchor⟩⟩
  soap:= bill L
  cost t i:= by
    let h:= L.legal t i
    refine ⟨fun q U=> ?_, ?_, fun u v he hp=>?_, fun U up hp x hx=>?_⟩
    · unfold bill whole enabled Healthy; rw [gauge_flags,h.symmetry]
    · by_cases he:L.clear i
      · simp_rw [funext (fun U=> show bill L t i U=0 from (by simp [bill,enabled,he]))]; exact measurable_const
      simp_rw [funext (fun U=> show bill L t i U= if Healthy P.p.threshold _ U then 0 else whole L t i U from (by simp [bill,enabled,he]; rfl))]; exact Measurable.ite (healthy_closed _ _).measurableSet measurable_const ((Overlay.Bands.sends _).measurable.comp h.borel) -- ns
    · have hy:Healthy P.p.threshold (L.ground i) u = Healthy P.p.threshold (L.ground i) v:= by
        unfold Healthy; simp only [Finset.disjoint_iff_inter_eq_empty]; rw [hp]
      simp only [bill,enabled,hy,whole,h.sites u v he]
    unfold bill at hp; split at hp; contradiction; unfold whole at hp; rw [Poly.part_send] at hp; split at hp; subst up; exact L.roots _ _ hx; exact (hp rfl).elim
  clean t i U h:= by
    unfold bill at h; split at h; contradiction
    exact fun hh=> ‹¬ enabled L i U› (Or.inr hh)
  skip t i U:=by unfold bill whole; split; rfl; rw [Poly.part_send,if_neg (show R.quiet ≠ L.mode i from L.live i|>.symm)]
  single t i U:=by
    unfold bill; split; rw [mul_zero]
    next he=> ext up; unfold whole; change (Poly.prod _ _).part up=0; rw [Poly.cart,if_neg (show ¬(Poly.merges (L.mode i) (L.mode i) up) from fun hx=> L.live _ (Subtype.ext (disjoint_self.mp hx.1)))]
local notation "θ"=> shifts L
lemma relates (t:T)(i:I)(U:Config G n): whole L t i U=L.frame i t U + (θ).soap t i U:= by
   change _= _+bill L t i U; unfold whole Lamps.frame Lamps.light bill
   split; next ht=> rw [if_pos (Or.inl ht: enabled L i U),add_zero]
   next ht=>
      by_cases h: Healthy P.p.threshold (L.ground i) U
      · rw [masked_eq _ _ _ _ h,if_pos (Or.inr h:enabled L i U),add_zero]
      rw [masked_ne _ _ _ _ h,if_neg (show ¬ enabled L i U from not_or.mpr ⟨ht,h⟩),Poly.send_zero,zero_add]; rfl
structure Global (w:V→ℝ)(a b:ℝ):Prop where
     grant : ∃ f:I→ℝ,(∀ i,0≤ f i)∧(∀ i t U, ‖L.nominal t i U‖ ≤ f i)∧ Rooted (fun i=>(L.mode i).val) L.ground P.p.B a (fun i=> Poly.toll w (L.mode i)*f i) b
variable {f:ℝ} {Y:Activities G n} (u:Kiosk.Second P.p Y (P.activities) b a P.p.supportExponent f)(hb:QuadraticLocal.Hard.Rent Y.forced Y.K P.p (P.p.supportExponent+1) b)
def set : Gallery T I o P R:=⟨ L,Kiosk.Second.canopy (QuadraticLocal.Hard.rent hb) (shifts L) u⟩
local notation "z"=> ( set L u hb )
local notation "g"=> Orbit.projections
include hw u hb
variable (h:(shifts L).Budget w P.p.B (P.p.supportExponent+1) f)(hp:1≤α)(hM:(Throng.Hard.shift (shifts L) α).Budget w P.p.B (P.p.supportExponent+1) f)
variable (hZ:L.Paid w P.p.B P.p.supportExponent k)
include h hZ
lemma reveals (t:T)(U: Config G n): Summable (fun i=> whole L t i U) ∧ (set L u hb).Pays w P.p.supportExponent k a ∧ (z).density t U= ( (↑(P.eval U):ℂ) ) • Poly.pass (∑' i, whole L t i U):= by
    let z₀:= set L u hb; let U' :=P.p; let ht:= QuadraticLocal.Hard.Rent.instals hw u hb (shifts L) P.p.exponent_pos.le h
    let A':= L.log t U; let Bx:= (shifts L).log t U
    have hr₀:0 ≤ P.p.supportExponent+1:= add_nonneg (P.p.exponent_pos.le) zero_le_one
    have hZ':= (shifts L).earnings h hw hr₀ t U
    have hW:= hZ.sums P.p.exponent_pos.le hw t U
    have hX: HasSum (fun i=> whole L t i U) (A'+Bx):= (hW.hasSum.add hZ'.hasSum).congr_fun (fun i=> relates L t i U)
    have hT: A'.part R.quiet=0:= Lamps.quiet_of_hasSum t U hW
    have hY: Bx.part R.quiet=0:= by unfold Bx Canopy.ShiftRows.log; rw [Poly.share hZ']; simp_rw [(shifts L).skip]; exact tsum_zero
    refine ⟨hX.summable,⟨hZ,ht.1⟩,?_⟩
    have he' : z₀.gas t U=(↑(P.activities.gas P.p U):ℂ) • Poly.pass Bx:= ( ht.2 t U ).tsum_eq
    rw [ Gallery.density, show (z).E.log t U=A' from rfl, show (z).gas t U=_ from he', hX.tsum_eq, ← GridRenewal.Rain.passes (A'+Bx) (show _=0 from (by simp only [Poly.part_plus,hT,hY,add_zero])), GridRenewal.Rain.plus,GridRenewal.Rain.passes _ hT,GridRenewal.Rain.passes _ hY,Rep.eval,Complex.ofReal_mul,mul_smul_comm, smul_smul]
omit h hZ
include hp hM
lemma echoes : Throng.Hard.Pair (z).K w P.p.B P.p.supportExponent a (α⁻¹*a):=by
   let H:= QuadraticLocal.Hard.rent (α:=T) (o:=o) (R:=R) hb
   have h: Throng.Hard.metal H α=H:= by unfold Throng.Hard.metal; congr 1; ext1 t; funext i V; change boom α (Poly.send R.quiet _) = Poly.send R.quiet _; exact scalar _
   refine Throng.Hard.Pair.theatre hp hw _ (Throng.Hard.president (shifts L) u hw P.p.exponent_pos.le hp H ?_ hM)
   rw [h]; exact QuadraticLocal.Hard.leasing hb
omit hw hp hM
open Affinity
variable {Λ:V→Support n}{E:V→Type}[∀ i, AddCommGroup (E i)][∀ i,Module ℝ (E i)]
variable {Actors:∀ i, Set (E i)} {uK:∀ i,Submodule ℝ (E i)}
variable {L':Lamps ( Affinity.Wallet Actors ) I G P.p o R}
lemma unchanged (hV:Affinity.Taut Λ Actors uK L'): Affinity.Collared Λ Actors uK P (set L' u hb):= by
   refine ⟨hV, Affinity.Crown.second _ u ( shifts L' ) ?_ (fun i U=>?_ )⟩
   · refine ⟨fun i u=> Affinity.Stencil.const (Poly.bead R (↑(Y.K i u):ℂ)) fun i hi=>?_⟩; exact (Poly.part_send ..).trans (if_neg hi)
   unfold shifts; dsimp only; refine ⟨fun s=> ?_⟩; unfold bill; split; exact Addressable.gone; next ha=> unfold whole; simp_rw [ Poly.part_send ]; split; exact (by rename_i hd; subst s; exact ⟨hV.adv i U,fun t' hp v hv=>hV.house i v hv⟩); exact Addressable.gone

omit u hb
-- cost payload lifted by α. Need Ψ polynomial post θ* * z-boost not marker count powers.
variable (Z:Global L w (P.p.supportExponent+2) t)
include Z hw
variable {μ:ℕ}(hσ:Occupancy o μ)
include hσ
local notation "τm"=> ( Aperture.muQ P.p μ )
-- This and mask-value budget from roots cost; physical coupling inverse powers already in tall Φ, if any.
lemma subscriber (he:0≤t) : (shifts L).Budget w P.p.B (P.p.supportExponent+1) ( τm * t ):= by
   obtain ⟨t',hu,hT,hP⟩:= Z.grant; let F i:= Poly.send (L.mode i) (t' i); refine ⟨F,fun i t U s=>?_,?_⟩
   · change ‖(bill L t i U|>.part s)‖ ≤ _ ∧ _; by_cases hp:s=L.mode i; swap; · unfold bill whole F; split; simp [hp]; simp [hp]
     subst s; unfold bill whole F; split; simp [hu]; rw [Poly.part_send,Poly.part_send,if_pos rfl,if_pos rfl]; exact ⟨hT i t U,rfl⟩ -- simp uses
   let q i:=Poly.toll w (L.mode i)*t' i; let f i:=(θ).place i; have hp i: Poly.price w (F i)=q i:= by unfold q F; rw [Poly.solo, Complex.norm_real,Real.norm_of_nonneg (hu i)]
   rw [funext hp]; refine Extra.Multi.root_hit (mode:=fun i=>(L.mode i).val) hσ («X»:=L.ground) (fun i=> mul_nonneg (Poly.worth hw _).le (hu i)) he ?_ ?_ 
   · intro i _; obtain ⟨v,hv⟩:= Finset.nonempty_iff_ne_empty.mpr (show (L.mode i).val≠∅ from fun hv=> L.live i (Subtype.ext hv)); exact ⟨v,hv,L.roots _ _ hv⟩
   rw [add_assoc]; norm_num; exact hP
omit Z hσ
lemma scaler (Qx: ShiftRows T I G P.p o R)(hq:Qx.Budget w B k t) (he:0≤α): (Throng.Hard.shift Qx α).Budget w B k (α*t):=by
    obtain ⟨f,hF,hG⟩:= hq.earned; let g' i:= (α:ℂ) • f i; refine ⟨g', fun i t U q=>?_ ,fun i=>?_⟩
    · have hh:= hF i t U q; change ‖((_:ℂ) • Qx.soap t i U).part q‖≤ _∧_; unfold g'; rw [Poly.part_smul,Poly.part_smul]; rw [Complex.mul_re, Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,norm_mul,Complex.norm_real,Real.norm_of_nonneg he,hh.2,mul_zero,zero_mul,add_zero,sub_zero]; exact ⟨mul_le_mul_of_nonneg_left hh.1 he,by simp⟩ -- trivial questionable
    simp_rw [g', Poly.adapted,Complex.norm_real, Real.norm_of_nonneg he]; convert budget_scale he (hG i) using 1; ext1 j; change (if i∈(Qx.place j).val then _ else _)=_ ; split; rw [mul_assoc]; exact rfl; rw [mul_zero]
end YM.QuadraticLocal.Neighborhood.Origin

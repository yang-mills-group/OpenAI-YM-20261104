import YM.AllOrder.Quay.Face
import YM.AllOrder.Rosary.Shive
import YM.Extra.WILSON_STARTUP.Cake
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Quay
open Function Filter Work Tensor Lattice Wilson RG Ovens Finset
open WilsonStartup WilsonStartup.Design WilsonStartup.Start WilsonStartup.Padded Floe Floe.Crest Till Tilt Burn
open PhysicalNext Repeat Pressure ConnectedActivityE6 ConnectedActivityE6.Coat Rosary
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {κ j k a c : ℕ}{σ ω' α T C:ℝ}
variable (p:BudgetPoint)(h:Clip)(β:ℝ)
-- group packets onto exactly the Tilt book platform. Fares analytic & Young E loan.
abbrev batch (x:Site n) (s:Signed)(q:PlaqAxes) : Key n := (s,x,q)
lemma sits (i:Key n) (hv:2≤p.B) : i.skin ⊆ court i.native p.B:= fun z hz=>halo_spec.mpr ⟨_,mem_singleton_self _,(i.nearby hz).trans hv⟩
variable (k)
local notation "B"=>p.B
local notation "Y"=>tile h G
local notation "w"=>weight h β
local notation "r"=>gStep β
lemma ceiling_tag (hk:0<β)(i:ℕ): Tilt.rates r (ceiling i)=β:= by
 let z:=r; have ht:0<z:= (by unfold z gStep; positivity); let j:= i+3; have he:= square_heat hk; change z^j*(z^(j+2))⁻¹= _; rw [pow_add]; field_simp; change β*z^2=1 at he; grind -- likely nonlin with z^j
lemma extent_len (v:Age)(q:ℕ): (tile h G v q).length=4*v.r:= by unfold tile; split <;> simp [Crest.place, Design.extractAtom, Extra.Iteration.blank, Atom.length, Design.plaquette, Slot.length,Nat.mul_comm]
lemma trunc (v:Age)(q:ℕ)(hg: 4*v.r≤p.B): legible (tile h G v) p.B q = tile h G v q:= scheme_of_fits B _ ((extent_len (G:=G) h v q).symm ▸ hg)
lemma unpriced (x:Site n)(U:Config G n)(v:Age)(hv:4*v.r≤p.B): Tilt.print (tile h G v) p.B n x U= share*∑ s: Signed, ∑' q:ℕ, (tile h G v q).unmasked (pull s x U) 0:= by
 rw [price_tag (tile h G v) x B (info h G v 1) zero_lt_one hv]; simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]; change share*_=_; apply congr_arg; apply Finset.sum_congr rfl; intro i _; change nextV.soul _ _ _ (pull i x U) =_; rw [nextV.plies (tile h G v) _ _ B (info h G v 1) zero_lt_one hv]; simp only [trunc p h v _ hv]
lemma payable (x:Site n)(U:Config G n)(v:ℕ): (∑' q:ℕ,(place h G v q).unmasked U x)=∑ i:PlaqAxes, bulk h * channel v (faceValue U (x,i)):= by refine totals (α:=PlaqAxes) ?_; intro i; unfold place; split <;> rw [Design.extract_unmasked] <;> simp only [headx, Tensor.diagonal, ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.zero_apply,smul_eq_mul]
local notation "S"=> Age.scope (k+2)
local notation "sM"=> offerS G p Y S r
variable (x:Site n)(U:Config G n)
lemma crown_juice (hk:4*(k+4)≤ p.B)(hb:0<β): (sM n x) U= weight h β *∑ s: Signed, ∑ q:PlaqAxes, fill k (faceValue (pull s x U) (0,q)):= by
 unfold offerS Tilt.patch Tilt.sundry; simp only [Finset.sum_apply,Pi.smul_apply, smul_eq_mul]; -- want restrict Scope to grid. formgrid requires prove outside 0 all, our trunc hv only inside. make `ScopeCond` or adapt formgrid.K
 have he v (hv:v∈Age.scope (k+2)) : Tilt.print (tile h G v) p.B n x U=_:= unpriced p h x U v ((Nat.mul_le_mul_left 4 (v.pricey.trans (Nat.add_le_add_right (Age.in_scope.mp hv) _))).trans hk);
 rw [Finset.sum_congr rfl (fun i hi=> congr_arg (Tilt.rates r i * ·) (he i hi)), formgrid (k)]; simp only [ceiling_tag β hb]; swap
 -- hp.Trivial.Nonpricing.th
 · intro i hi; simp [tile,hi, Extra.Iteration.blank, Atom.unmasked,Atom.poly];
 have hp(i:ℕ)(s:Signed):(∑' q:ℕ, ((Y (ceiling i)) q).unmasked (pull s x U) 0)=∑ b:PlaqAxes, bulk h * channel (i+5) (faceValue (pull s x U) (0,b)):= by rw [yes]; apply payable
 simp_rw [hp]
 unfold Start.weight Crest.fill; simp_rw [← mul_sum]; -- check mul_sum direction
 ring_nf; refine congr_arg (β*share*bulk h * ·) ?_; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_comm
end YM.AllOrder.Quay

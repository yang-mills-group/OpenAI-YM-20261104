import YM.OPE.Therm.Caprice
/-!
# Use the *actual* local truncation of the energy

Adapted disjoint-reads argument from Therm/CorePatch.lean. Use concentric finitary exteriors
and keep denominators. Every tap of every patch has one outer circle including threshold read
sets. This only compares local expectations, not a general transport theorem for normalized
ratios of arbitrary marked densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG20
open Function Filter Set MeasureTheory Lattice Wilson RG OPE.Therm House Cradle Portolan
open scoped BigOperators ContDiff Topology Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {R : Rep G n} {r q t : ℕ} {τ C e : ℝ}
  {z : Site n} {A : Finset (Edge (Site n))} {f : Config G n → ℝ}
local notation "𝒞" => Config G n
local notation "Q" => Stove.haloFee R r
local notation "Z₀" => Stove.energy R r
local notation "Ex" => Real.exp
local notation "η" => prior G n

section geometry

lemma coat_extend (z : Site n) (h : q ≤ t) : coat q z ⊆ coat t z :=
    link_mono (fun _ hx => region_increase h hx)

lemma border_extend (z : Site n) (h : q ≤ t) : border R r q z ⊆ border R r t z :=
    region_increase (Nat.add_le_add_right h _)

lemma schedule_extend (z : Site n) (h : q ≤ t) : schedule q z ⊆ schedule t z :=
  fun _ hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, region_increase (Nat.add_le_add_right h _) ((Finset.mem_filter.mp hx).2)⟩

lemma essence_nonneg (V : Config G n) : 0 ≤ essence R r τ q z V :=
  mul_nonneg (Real.exp_pos _).le (tapes_non ..)

lemma chilled_health (h : τ ≤ R.p.threshold) (V : Config G n)
    (hv : essence R r τ q z V ≠ 0) : Healthy R.p.threshold (region q z) V := by
  have hx : V∈ chilly (schedule q z) τ := by
    by_contra he; exact hv (by rw [essence, tape, if_neg he, mul_zero])
  refine Finset.disjoint_left.mpr fun x hx' hh => ?_
  obtain ⟨i,hi,ht⟩:= (flags_spec ..).mp hh
  refine not_lt_of_ge ((hx i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,region_mem.mpr ?_⟩)).trans h) ht
  exact (separation_triangle _ x _).trans (Nat.add_le_add (region_mem.mp hx') ((separation_comm _ _).trans_le (Work.E01.sep_touched i _ hi)))

section
variable (Y : Stove.Chart R r C e)
include Y
lemma essence_fenced (h : parcel R r q ≤ t) : fence (coat t z) (essence R r τ q z) := by
    refine local_fence.mpr ?_
    intro U V hv
    have he x (hx : x∈border R r q z) : Z₀ x U = Z₀ x V := by
      refine Y.home x _ _ (agrees_mono hv fun i hi=> ?_)
      refine region_mem.mpr ((separation_triangle z x i).trans ?_)
      have hf:= region_mem.mp (show x∈region (q+Stove.haloFee R r) z from hx)
      have ht:= region_mem.mp (show i∈region (Stove.haloFee R r) x from hi)
      unfold parcel at h; omega
    unfold essence; rw [Finset.sum_congr rfl he]
    apply congr_arg
    have hh : U∈chilly (schedule q z) τ ↔ V∈chilly (schedule q z) τ:= forall₂_congr fun i hi=> by
       have ht:faceValue U i=faceValue V i:= by
         apply travel_local; refine agrees_mono hv fun x hx=>region_mem.mpr ((separation_triangle _ i.1 _).trans ?_)
         have hu:=region_mem.mp (show i.1∈region (q+2) z from (Finset.mem_filter.mp hi).2)
         have hw:= Work.E01.sep_touched i x (List.mem_toFinset.mpr hx)
         unfold parcel at h; omega
       rw [ht]
    unfold tape; simp_rw [hh]

/-- For using an outer testing scope without invalidating the inner kernel. -/
lemma collared (ha : A ⊆ coat q z) (ht : q ≤ t) : ∃ F' : Config G n → ℝ,
    stills A F' ∧ Envelope F' ∧ (∀ U, 0 ≤ F' U) ∧
      essence R r τ t z= fun U => F' U * essence R r τ q z U := by
   let P := border R r t z; let S:=border R r q z; let D:=P\S; let f (U:𝒞):=-(∑ x∈D,Z₀ x U)
   let H:=schedule t z; let J:=schedule q z; let G₀:=H\J
   have he' : J⊆H:= schedule_extend z ht; have hT : S⊆P:=border_extend z ht
   have hl x (hx:x∈ D): stills A (Z₀ x):=by
      refine spares (local_fence.mpr (Y.home x)) (Disjoint.mono_right ha ?_); apply orbits (s:=Q) (t:=q); rw [add_comm,separation_comm]; exact lt_of_not_ge (fun he=> (Finset.mem_sdiff.mp hx).2 (region_mem.mpr he))
   have hu x (hx:x∈G₀) : Disjoint A (links (↑(touched x):Set _)):=by
      refine Disjoint.mono_left ha (Finset.disjoint_left.mpr fun e h₁ h₂=>?_); apply (Finset.mem_sdiff.mp hx).2; apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,region_mem.mpr ((separation_triangle _ e.1 _).trans ?_)⟩; exact Nat.add_le_add (region_mem.mp ((linn.mp h₁).1)) ((separation_comm e.1 x.1).trans_le (Work.E01.sep_touched x e.1 (linn.mp h₂).1))
   refine ⟨fun U=>Ex (f U)*tape G₀ τ U, fun U V hp=>?_, Envelope.mul (Envelope.exp (Envelope.neg (Envelope.sum _ _ fun i=>⟨Y.bill i,C,Y.paid i⟩))) (tape_env G₀),fun U=>mul_nonneg (Real.exp_pos _).le (tapes_non ..), funext fun U=>?_⟩
   · unfold f; dsimp only; rw [show (∑ x∈D,Z₀ x U)=(∑ x∈D,Z₀ x V) from Finset.sum_congr rfl fun i hi=> hl i hi U V hp, still_tape hu U V hp]
   change Ex (-(∑ x∈P,Z₀ x U))*tape H τ U=_; have hh : tape H τ U=tape G₀ τ U*tape J τ U:=by rw [← tapes, Finset.sdiff_union_of_subset he']
   dsimp only; rw [hh, ← Finset.sum_sdiff hT, neg_add,Real.exp_add]; unfold essence f G₀ D J S H P; ring
end
end geometry

-- model kernel. Don't interpret denominator as true conditional; rather
-- numerator/denominator of explicitly DEFINED next computation. True δ obligation below.
def recoup (A:Finset (Edge (Site n))) (w f : Config G n → ℝ) (U:Config G n) :=
    press A (fun V=> f V*w V) U / press A w U

section
variable {w:Config G n→ℝ}{s : ℝ}

lemma pressed_fence {B:Finset (Edge (Site n))} (hf:fence B f) : fence B (press A f):=by
   intro U V h; apply integral_congr_ae; refine Eventually.of_forall fun u=> hf _ _ fun e he=> ?_
   unfold meld; split; rfl; exact h he
lemma recoup_fence {B:Finset (Edge (Site n))} (hf:fence B f)(hw:fence B w) : fence B (recoup A w f):=by
   intro U V h; unfold recoup
   apply congr_arg₂ HDiv.hDiv (pressed_fence (f:=fun i=>f i*w i) (fun i j ht=> ?_) U V h) (pressed_fence hw U V h)
   simp_rw [hf i j ht,hw i j ht]
lemma recoup_still : stills A (recoup A w f):=fun U V h=> congr_arg₂ HDiv.hDiv (dormant A _ U V h) (dormant A w U V h)

lemma positive_bill (H : ∀ U,0≤ w U) (U:Config G n) : 0 ≤ press A w U := integral_nonneg (fun _=> H _)

variable (hs: Envelope w) (H : ∀ U,0≤ w U)
include hs H
lemma bill (hf:Envelope f) (h : ∀ U,‖f U‖≤ s) (U:Config G n):
    ‖press A (f*w) U‖ ≤ s * press A w U:= by
   have hv' : (∀ U, -s * w U ≤ f U*w U) ∧ ∀ U, f U*w U≤ s*w U:= by
     constructor
     · exact fun U=> mul_le_mul_of_nonneg_right (abs_le.mp (h U)).1 (H U)
     exact fun U=>mul_le_mul_of_nonneg_right (abs_le.mp (h U)).2 (H U)
   have he (x:ℝ) : press A (fun V=> x*w V) U=x*press A w U:= integral_const_mul ..
   have ht:=hf.mul hs
   rw [Real.norm_eq_abs, abs_le]; constructor
   · rw [← neg_mul, ← he]; exact press_mono _ ((Envelope.const _).mul hs) ht hv'.1 U
   rw [← he]; exact press_mono _ ht ((Envelope.const _).mul hs) hv'.2 U

lemma zero_bill (hf:Envelope f)(U:Config G n) : recoup A w f U* press A w U= press A (f*w) U:=by
   by_cases hm: press A w U=0
   · rw [hm,mul_zero]; symm; apply norm_eq_zero.mp; obtain ⟨v,h⟩:= hf.cost; exact le_antisymm (by simpa only [hm,mul_zero] using bill (A:=A) hs H hf h U) (norm_nonneg _)
   exact div_mul_cancel₀ _ hm
lemma recoup_bound (h:∀ U, ‖f U‖≤ s)(hf:Measurable f) (U:Config G n) : ‖recoup A w f U‖ ≤ s:=by
    unfold recoup; rw [norm_div,Real.norm_of_nonneg (positive_bill H _)]
    by_cases hv: press A w U=0
    · rw [hv,div_zero]; exact (norm_nonneg _).trans (h U)
    exact (div_le_iff₀ (lt_of_le_of_ne (positive_bill H _) (Ne.symm hv))).mpr (bill hs H ⟨hf,s,h⟩ h U)
lemma recoup_env (hf:Envelope f) : Envelope (recoup A w f):=by
   obtain ⟨s,h⟩:= hf.cost; exact ⟨(held_mass A (hf.mul hs)).meas.div (held_mass A hs).meas,s,recoup_bound hs H h hf.meas⟩

/-- Handles all inputs including zero denominator: choose sub-probability
convention to track their full loss explicitly. -/
lemma centered_press (hf:Envelope f) (U:Config G n) : press A (fun U=> (f U-recoup A w f U)*w U) U=0:=by
   let K:= recoup A w f
   have hK:=recoup_env (A:=A) hs H hf
   rw [show (fun U=>(f U-recoup A w f U)*w U) = (fun U=> f U*w U + -(recoup A w f U*w U)) from funext fun U=>by ring,
     press_add _ (hf.mul hs) (hK.mul hs).neg]
   have he : press A (fun U=> -(K U*w U)) U = - press A (fun U=> K U *w U) U:= integral_neg ..
   rw [show _=_ from he, pressmulL w recoup_still, zero_bill hs H hf]; exact add_neg_cancel _

end
end YM.RG20

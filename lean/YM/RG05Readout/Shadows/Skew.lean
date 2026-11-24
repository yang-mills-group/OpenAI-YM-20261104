import YM.RG05Readout.Capture.Fronds
/-!
# Arbitrary per-child representatives

The cost reach before comparison is skewed: even while all copies read
an identical product, their polymer accounting needn't be equivariant.
Price a skew step in the null space with different log/forced profiles (and
even different densities). Uses `stitch` directly, not `Train` on equality
of the density or equating arbitrary π on different directed origins.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{N m p d:ℕ}
    {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {B B' e :ℝ}
set_option quotPrecheck false
local notation "Z"=> (C.path.levels.clock.op m p)
local notation "R!"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "Kc"=> kappa C.path
local notation "O"=> Bud C p m
local notation "ψ"=> child C p m
local notation "L"=> C.path.S.block m
local notation "λ₀"=>(((L).val:ℝ)^d)
local notation "v₀"=> wrap_price d C* Trace.Physical.Germ.wraps (M).p (C.side (m+1) p)
local notation "v₁"=> wrap_price d C* Trace.Physical.Germ.wraps (R!).p (C.side m p)
variable (h:C.Makes)(hm:m<N)(u:∀ i:Bud C p m,(C.path.rep N p (m+1)).activities.Moves 1 (child C p m i))
variable (hc:SignedPrice C m p d N D B B')
local notation "ℓ"=> ld C.path.levels m
local notation "δ"=> displacement C p m
local notation "q"=> trim L

lemma snapshotAve {U:Type*} [Fintype U][Nonempty U]{n:Side}{t e b c v y z:ℝ}{R:Rep G n}
    {P:U→Tape G n}{a b':U→Palette C d}
    (hp:0<t)(hR:R.Lawful b c v y z)(hx: d≤ R.p.order)(hu:d≤ R.p.power)
    (h:∀ i,Printed C d R 0 t (P i) (a i) (b' i) e): Printed C d R 0 t (average P) (average a) (average b') e:=by
    let e':=(Fintype.card U:ℂ)⁻¹
    apply ((Printed.all hp hR Finset.univ hx hu (fun i _=> h i)).twist hx hu e').grow
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,norm_inv, Complex.norm_natCast,←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne_zero),one_mul]
section
include h hm hc
set_option maxHeartbeats 600000 in
lemma dark_skew {s₀:ℝ}(P: Address.Bud C p m→Tape G (C.side (m+1) p))(X:O→Palette C d)(hp:∀ i, Printed C d M 0 (Kc (m+1)) (P i) (X i) 0 s₀)
    (V:Palette C d→ₗ[ℂ]Tape G (C.side m p))(hy: Group C N m p d V B'):
    ∃ (f:O→Tape G (C.side m p)) (y:Palette C d), (∀ i,Travel C N m p d (ψ i) D ((orient u (P i) i).comp (Many.headFee C p m i)) (f i) (ℓ*s₀))∧ size y ≤ q*s₀ ∧ ∃ z:Palette C d, Printed C d R! 0 (Kc m) ((average f) - V y) z 0 (q*s₀):=by
    obtain ⟨s,K,c,β,T,Q,H,hT,hX,hu,hW,hxz,hf,hδ,hV,hζ⟩:= hc.author
    let α:= Doors.rate L; let Ω:=margin d c K; let η:= decay d L K c α*shiftFee (M).p; let b:= Ω*((L).val:ℝ)⁻¹+η; let a:= Ω*(λ₀ * v₀)+η
    let w:= (1+v₁)*a
    have hl:0 ≤ Ω:=mul_nonneg (add_nonneg (sCpos (zero_le_one.trans H.cursor.fits)) (aCpos (zero_le_one.trans H.cursor.fits))) (zero_le_one.trans H.posp)
    have he:0≤ s₀:=(hp 0).nonneg
    have hΩ:0≤ η:= mul_nonneg (decays L (zero_le_one.trans H.cursor.fits) (zero_le_one.trans H.posp) (Doors.rate_pos _).le) (zero_le_one.trans shift_pays)
    have hz:0≤ a:= by unfold a; have h:= mul_nonneg (a:=wrap_price d C) (b:=(Trace.Physical.Germ.wraps (M).p (C.side (m+1) p))) (zero_le_one.trans (price_nn ..)) (Real.exp_pos _).le; positivity
    have hc₁:B ≥ 1:= hc.pos.1; have hc₂:B' ≥ 1:=hc.pos.2; let X0:=L
    obtain ⟨hb',hb⟩:= max_le_iff.mp hu
    have hu0:v₀ ≤ thin L d:=by rw [(h.wilson.represents N p _ hm).vac]; exact hb
    have hu1:v₁ ≤ thin L d:=by rw [(h.wilson.represents N p m hm.le).vac]; exact hb'
    have hu: λ₀*v₀ ≤ ((X0.val:ℝ)⁻¹):=(mul_le_mul_of_nonneg_left hu0 (pow_nonneg (by positivity) _)).trans_eq ((mul_comm ..).trans (small_power ..))
    have ha : a ≤ b := add_le_add_left (mul_le_mul_of_nonneg_left hu hl) _
    have hw : w ≤ 2*b:= mul_le_mul (le_trans (add_le_add_right (hu1.trans (thin_one ..)) _) (le_of_eq (one_add_one_eq_two))) ha hz zero_le_two
    have hr := h.wilson.represents N p m hm.le; let P':=H.cursor.sense d le_rfl
    have hy(i:O):∃ (f:Tape G (C.side m p)) (x z:Palette C d), Travel C N m p d (ψ i) D ((orient u (P i) i).comp (Many.headFee C p m i)) f (ℓ*s₀) ∧ Printed C d R! 0 (Kc m) f x z (a*s₀)∧ size z ≤ w*s₀:=by
       obtain ⟨l,hP⟩:= moveprint (ψ i) (u i) (P i) (X i) 0 ((by decide : 2≤4).trans (Next.Foundations.actual_side_ge ..)) h (hp i)
       let V:=orient u (P i) i; obtain ⟨g,q',r,he'⟩:= slip h hm (ψ i) (Bud.personal ..) H (dist_box C p m i)
       obtain ⟨U,v,x,hp0,hQ⟩:= stitch h hm (ψ i) (Bud.personal ..) H (dist_box C p m i) V (X i) l _ hP he'
       let y:= size (amplify d C L (X i)); have hx:=wraps_paid d C (hp i) hT.bound hT.bill; rw [zero_sub,size_neg] at hx; have hJ : y≤ (λ₀*v₀)*s₀:= ((size_tuned ..).trans (mul_le_mul_of_nonneg_left hx (pow_nonneg (by positivity) _))).trans_eq (mul_assoc ..).symm
       have hXP:Ω*y+ decay d L K c (Doors.rate L)*(shiftFee (M).p*s₀)≤ a*s₀:= le_trans (add_le_add_left (mul_le_mul_of_nonneg_left hJ hl) _) (le_of_eq (by unfold a η α;ring))
       have hm0:=hp0.paid.grow hXP; refine ⟨U,v,x,hp0.ready.extend ?_,hm0,?_⟩
       · let v:= tollV d L K c α β*shiftFee (M).p; let M':=tollP d K c β; have hs' := H.b_pos; have hj:= zero_le_one.trans H.cursor.fits; have hx:0 ≤ M':=mul_nonneg (aCpos hj) (by have hz:=H.posp; positivity)
         have hh : M'*(λ₀*v₀) + v ≤ ℓ :=by
            apply le_trans ?_ hW
            have he := (mul_le_mul_of_nonneg_left hu hx).trans (mul_le_of_le_one_right hx (inv_le_one_of_one_le₀ (by exact_mod_cast X0.property)))
            exact add_le_add (he.trans (by linarith only [hx])) (le_mul_of_one_le_right hT.loop hc₁)
         change M'*y+tollV d L K c (Doors.rate L) β * (shiftFee (M).p*s₀) ≤ _; rw [← mul_assoc (tollV ..)]
         have ht':= mul_le_mul_of_nonneg_left hJ hx
         exact le_trans (add_le_add_left ht' _) ((le_of_eq (by unfold v α; ring)).trans (mul_le_mul_of_nonneg_right hh he))
       have hy:size v ≤ a*s₀:= le_trans (size_compare v _) ((add_le_add (echo_bill L q' he'.age (X i)) hQ).trans hXP)
       exact le_trans (size_compare x v) ((add_le_add hy (wraps_paid d C hm0 P'.order P'.power)).trans_eq (by unfold w; ring))
    choose f x z hF hP hZ using hy
    have hB:= snapshotAve (Real.sqrt_pos.mpr (forcedPos C.path.levels m)) hr.good P'.order P'.power hP
    let y:=average z; have hZ': size y≤ w*s₀:=ave_size _ hZ
    obtain ⟨z',hq⟩:= (show Group C N m p d V B' from ‹_›).capacity0 (-y); rw [size_neg] at hq;
    have hP':= hB.addP hq hr.good P'.order P'.power; unfold y at hP'; rw [map_neg,add_neg_cancel] at hP'
    refine ⟨f,y,hF,hZ'.trans ?_,(average x+z'),?_⟩
    · exact mul_le_mul_of_nonneg_right (hw.trans (le_trans (le_trans (le_mul_of_one_le_left (show 0 ≤ 2*b from mul_nonneg zero_le_two (hz.trans ha)) hc₂) (le_add_of_nonneg_left (hz.trans ha))) hX)) he
    rw [sub_eq_add_neg]; apply hP'.grow
    apply (add_le_add_right (mul_le_mul_of_nonneg_left hZ' (zero_le_one.trans hc₂)) _).trans
    have hx' : a+B'*w≤ q:= (add_le_add ha (mul_le_mul_of_nonneg_left hw (zero_le_one.trans hc₂))).trans hX
    exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_right hx' he)
end
end YM.RG05Readout.Address

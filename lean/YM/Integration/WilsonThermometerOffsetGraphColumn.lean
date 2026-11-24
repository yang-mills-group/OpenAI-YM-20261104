import YM.Integration.WilsonThermometerOffsetTransfer

/-! One inherited physical source on a chosen child. Keep its actual
within-cell test and both finite-period wrapping errors on the original door. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetGraphColumn
open RG05Readout RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical RG05Readout.Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{N m p d:ℕ} {s K α β γ A c t e:ℝ}
    {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "Kc"=> kappa C.path
local notation "O"=> Bud C p m
local notation "ψ"=> child C p m
local notation "L"=> C.path.S.block m
local notation "λ₀"=>(((L).val:ℝ)^d)
local notation "I"=> Palette C d
local notation "J"=> Mark C d
local notation "tilt"=> amplify d C L
local notation "η'"=> decay d L K c α* shiftFee (M).p
local notation "ϑ"=> tollP d K c β
local notation "π"=> tollV d L K c α β*shiftFee (M).p
local notation "Ω"=> margin d c K
local notation "v₀"=> wrap_price d C* Trace.Physical.Germ.wraps (M).p (C.side (m+1) p)
local notation "v₁"=> wrap_price d C* Trace.Physical.Germ.wraps (R).p (C.side m p)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))} (hw:Plot D s K c α β T)
variable {u:∀ i:Bud C p m,(C.path.rep N p (m+1)).activities.Moves (1:Signed) (child C p m i)}


include hw

/-- Input and output retain their genuine finite-period coordinates, including the
charged difference between the stored and measured coordinates at both ends. -/
theorem received {V : I →ₗ[ℂ] Tape G (C.side (m+1) p)} {B : ℝ}
    (h : C.Makes) (hm : m<N) (H : Group C N (m+1) p d V B)
    (hc : Turns (K:=K) (β:=β) (c:=c) (α:=α) (γ:=γ) C N m p d B)
    (b : Bud C p m) :
    ∀ i : J, ∃ (U : Tape G (C.side m p)) (w z : I),
      size z ≤ (Ω+1)*chargeN L i ∧
      Printed C d R 0 (Kc m) U w z (ahead K c d*chargeN L i) ∧
      Travel C N m p d (ψ b) D
        ((orient u (V (ticket i)) b).comp (Native.pull (displacement C p m b) ((L).val:ℝ)⁻¹))
        U ((2*ϑ+π*B)*chargeN L i) ∧
      size (Address.clear C d (weights i) (z-leadScale C L i (T i.1))) ≤ γ+oldCost d K*α := by
     obtain ⟨Y,l,y,slot⟩ := slip h hm (ψ b) (Bud.personal C p m b) hw (dist_box C p m b)
     intro i
     obtain ⟨pα,hR⟩ := H.capacity0 (ticket i)
     rw [size_ticket,mul_one] at hR
     let F := V (ticket i)
     obtain ⟨x',hP⟩ := moveprint (ψ b) (u b) F pα (ticket i)
       ((by decide : 2≤4).trans (Next.Foundations.actual_side_ge ..)) h hR
     obtain ⟨U,w,k,step,hs⟩ := stitch h hm (ψ b) (Bud.personal C p m b) hw (dist_box C p m b)
       _ pα x' _ hP slot
     have hF := step.paid
     have hV := step.ready
     rw [← mul_assoc (decay ..)] at hs
     rw [← mul_assoc (decay ..)] at hF
     rw [← mul_assoc (tollV ..)] at hV
     have hx := hs
     let mu:=chargeN L i; have hi : 1 ≤ mu:=charge_one L i
     let f:=v₀*B
     have hf:size (pα-ticket i) ≤ f:=by rw [size_turn]; exact wraps_paid d C hR hc.bound hc.bill
     let y:=size (tilt pα); have hT: size (tilt (ticket i))=mu:=by rw [ticket_charge,size_smul,size_ticket,mul_one,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hi)]
     have ht' : size (tilt (pα-ticket i)) ≤ λ₀*f:= (size_tuned ..).trans (mul_le_mul_of_nonneg_left hf (by positivity)); let V':=Slide pα l
     have hx' : y ≤ 2*mu:=by
          apply (size_compare _ (tilt (ticket i))).trans
          rw [hT,← map_sub]; have hκ:=ht'.trans hc.rear
          linarith only [hκ,hi]
     have hΦ : size (V'-l i) ≤ Ω*(λ₀*f):=by
          let p:Palette C d→ₗ[ℂ]I:= (slide_linear l).mk' _; rw [←ticket_self i l]
          change size (p _-p _) ≤ _; rw [← map_sub]
          exact (echo_bill L l slot.age _).trans (mul_le_mul_of_nonneg_left ht' (mul_nonneg (add_nonneg (sCpos (zero_le_one.trans hw.cursor.fits)) (aCpos (zero_le_one.trans hw.cursor.fits))) (zero_le_one.trans hw.posp)))
     have hΩ:0 ≤ Ω:= mul_nonneg (add_nonneg (sCpos (zero_le_one.trans hw.cursor.fits)) (aCpos (zero_le_one.trans hw.cursor.fits))) (zero_le_one.trans hw.posp)
     have hp : Printed C d R 0 (Kc m) U w k ((ahead K c d)*mu):=by
          apply hF.grow; change Ω*y+η'*B≤ _
          apply (add_le_add (mul_le_mul_of_nonneg_left hx' hΩ) hc.grasp).trans; unfold ahead; linarith only [hi]
     have ha:=hw.cursor.sense d le_rfl
     have hc₁ : 0 ≤ v₁ := mul_nonneg (zero_le_one.trans (price_nn ..)) ((Real.exp_pos _).le)
     have hv:size (k - w)≤ v₁*((ahead K c d)*λ₀):= le_trans (wraps_paid d C hp ha.order ha.power) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (charge_global ..) (by unfold ahead; positivity)) hc₁)
     have hj:size (k-l i) ≤ γ:=le_trans ((le_of_eq (congr_arg size (show k-l i=(k-w)+(w-Slide pα l)+(Slide pα l - l i) from by abel))).trans ((size_add ..).trans (add_le_add ((size_add ..).trans (add_le_add hv hx)) hΦ))) hc.shave
     refine ⟨U,w,k, (size_compare k (l i)).trans ((add_le_add (slot.age i) (hj.trans (hc.cap.trans hi))).trans_eq (by ring)), hp,?_,?_⟩
     · refine hV.extend ?_; have ht0 : 0≤ ϑ:=by unfold tollP; have hpp:= aCpos (d:=d) (zero_le_one.trans hw.cursor.fits); have hK:=zero_le_one.trans hw.cursor.fits; have hb:=hw.b_pos; have hc:=hw.posp; positivity
       have hs := mul_le_mul_of_nonneg_left hx' ht0; have hk:= H.pos
       have he : π*B ≤ π*B*mu:= le_mul_of_one_le_right (mul_nonneg hc.loop (zero_le_one.trans hk)) hi
       change ϑ*y+_ ≤ _ * mu; linarith only [he,hs]
     exact (le_of_eq (congr_arg (fun z:Palette C d=> size (Address.clear C d (weights i) z)) (show k-leadScale C L i _=(k-l i)+(l i-leadScale C L i (T i.1)) from by abel))).trans (by rw [map_add]; exact (size_add ..).trans (add_le_add ((size_cap ..).trans hj) (slot.debits i)))

end YM.Integration.WilsonThermometerOffsetGraphColumn
end

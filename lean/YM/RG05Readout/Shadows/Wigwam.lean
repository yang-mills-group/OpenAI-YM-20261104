import YM.RG05Readout.Shadows.Wake
/-!
# The signed calculation on the projected product polynomial

Youngest step with two recurrences, counterterm uses exact inverse chosen
from an earlier (possibly narrower) representation at that site. Works
for coherent products across all actual alternative branches. No assuming
any output near-null bound; derive.*R actual phases/restoration applied by client
on the rootT values. Unit prices realized with more than room on aperture.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N n b m p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ} {x e E a r R:ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op n p
local notation "L"=> C.S.block n
local notation "F₀" => Palette C d
local notation "κ₁"=> kappa C.path
local notation "ℓ"=> Copper.ld C.path.levels n
local notation "ν₁"=> C.path.levels.clock.J
local notation "O"=> Address.Bud C p n
local notation "χ"=> ((C.path.S.block n).val:ℂ)^d
local notation "X'"=> R₀ (n+1)
local notation "X"=> R₀ n
local notation "Ch"=> Address.child C p n
local notation "Z₀"=> C.path.levels.budget
local notation "δ0"=> renal C.path.levels
local notation "TR"=> (fun i:O=> Many.headFee C p n i)
variable (hw:Awake D B b d)(hv:Spine D B h b p d N V S) (hc:Cater C D)
section
variable {F:Goods G (C.side (n+1) p)}{w:PulseC}
variable {H:∀ i:ℕ,Tape G (C.side i p)} {Y:ℕ→Palette C d} (ht: Signature C p b n N d h D V (amplitude C n N p d w F) e Y H)
    (hm:b ≤ n)(hN:n<N)(hg:12 ≤ C.path.levels.clock.J b)
local notation "z'" => advances S Y b n
abbrev repayment {C:Family G}{d:ℕ}(S:Emblems C d)(Y:ℕ→Palette C d) (b n:ℕ):= (S n).symm (Y n - advances S Y b n)
local notation "M'"=> repayment S Y b n
noncomputable def burden (C:Family G)(n d:ℕ)(e:ℝ):ℝ:= (Copper.ld C.path.levels n)^2*(2*e+20*bid C n d e)
include h hv ht hm hN hg
lemma arms_paid : Train (D N p n hN) (keys0 h hN) (d:=d) (V (n+1) M') (V n (Y n - z')) (burden C n d e):=by
    have hA:= hv.follows n hm hN; have hQ:= hA.goes M'; have hR:= hA.strength M'; let x:= Y n - z'
    have hJ: S n M'=x:=(S n).apply_symm_apply ..; rw [hJ] at hQ hR
    apply hQ.easier; apply le_trans (mul_le_mul_of_nonneg_left hR.1 (zero_le_one.trans (lamp_nn _))); have hu:= overture h hv hg hN.le (by -- e≥...
          obtain ⟨k,h⟩:= ht.rolls.empty n hm le_rfl; have ht:= h.nonneg; rw [tab_one] at ht; exact ht) ht.rolls.spends hm le_rfl; rw [tab_one] at hu
    have he:size x ≤ 2*e+20*bid C n d e:=by unfold x; rw [sub_eq_add_neg]; apply (size_add ..).trans; rw [size_neg]; exact add_le_add ht.pays hu
    unfold burden; rw [pow_two,← mul_assoc]; exact mul_le_mul_of_nonneg_left he (mul_nonneg (zero_le_one.trans (lamp_nn _)) (zero_le_one.trans (lamp_nn _)))
local notation "B₀"=> debit C n d a
local notation "B₁"=> burden C n d e
noncomputable def fare (C:Family G)(n d:ℕ)(a e:ℝ):= debit C n d a + burden C n d e
local notation "K"=> fare C n d a e
-- single signed coherence at parent.
variable (t: Motion)(o:Site (C.side n p)) (Q P: Address.Bud C p n→Three G (C.side (n+1) p))
local notation "y!"=> fun i:O => affine t.1 ((Ω).ratio.embed o) (Ch i)
include hw hc
set_option maxHeartbeats 700000 in
lemma earns (φ:Body)(π:(C.path.rep N p n).activities.Moves t.1 o)(hp:d+3 ≤ ν₁ n)(hV: Eden (N:=N) o t Q a F)(hW: Priced d w 1)(ha:0≤a)(hφ:Cap (d+2) φ 1)(hP:∀ i:O, Useful (X') (P i)∧ Signpost (X') t (y! i) (V (n+1) M' (TR i φ)) (P i)) :
    ∃ (A:Tape G (C.side n p))(U:O→Three G (C.side n p)), pulseOut A=pulseOut (H n)∧ (∃ z, Printed C d (X) 0 (κ₁ n) A z 0 (bid C n d B₀))∧ spin t π ((A+V n z') φ)= Address.average U ∧ ∀ i:O, Ride Ω (y! i) o (D N p n hN) χ ((scalar t (w (TR i φ))) • Q i - P i) (U i) K:=by
    let y:=Y n-z'; obtain ⟨T,f,g,hF,hT,hX,hq⟩:=morning h hw o t w hV hc hm hN hp ha hW
    obtain ⟨s,K',c,b',T',Q',hS,-⟩:= (hw.toll p n N hm hN).author; let a₀:= hS.cursor.sense d le_rfl
    let x:= Address.average T; have hP':= h.wilson.represents N p n hN.le; have hy := snapshotAve (Real.sqrt_pos.mpr (forcedPos C.path.levels n)) hP'.good a₀.order a₀.power hT
    obtain ⟨hx, hy,h0⟩:= roots_same h hw hv hm hN ht (Address.average T) hF hy (ave_size _ hX); rw [hx] at hy
    obtain ⟨U,hU,hA⟩:= report_one ‹C.Makes› hS.door t o _ _ φ d B₁ hN π (arms_paid ‹C.Makes› hv ht hm hN hg) hφ
    let D₁:= T∘id
    let Tq i:= spin t π (T i φ)
    let A:Tape G (C.side n p):= Address.average T - V n (Y n)
    refine ⟨A,Tq+(- (1:ℂ)) • U,hy,h0,?_,fun i=>?_⟩
    · rw [show A+ V n z'= Address.average T - V n (Y n-z') from by unfold A;rw [map_sub];abel, sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply,spin_add,show spin t π (- (V n (Y n-z') φ)) = - (1:ℂ) • (spin t π ((V n (Y n-z')) φ)) from ?_,ave_add, ave_smul, hU]
      · unfold Address.average; rw [LinearMap.smul_apply,LinearMap.sum_apply,spin_real,spin_sum]
        unfold Motion.scalar;split;simp;rfl
      have hl := spin_real t π (P:=V n (Y n-z') φ) (-(1:ℂ)) (by unfold Motion.scalar; split; simp; rfl)
      simp only[neg_smul,one_smul] at *; exact hl
    have hl: Ride Ω (y! i) o (D N p n hN) χ (- P i) ((- (1:ℂ) • U) i) B₁:=by
       have hl:=(hA i (P i) (hP i).1 (hP i).2).matchPay (-1) (-1) χ (mul_comm ..); simpa only [Pi.smul_apply,neg_smul,one_smul,norm_neg,norm_one,max_self,one_mul] using! hl
    rw [sub_eq_add_neg]; exact (hq i φ π hφ).taller hl hS.door (C.path.levels.transition_mass ..) (‹C.Makes›.wilson.represents _ _ _ hN).good hP'.good

end
end YM.RG05Readout.Shadow

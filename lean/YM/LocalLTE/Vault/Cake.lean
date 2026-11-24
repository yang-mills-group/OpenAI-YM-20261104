import YM.LocalLTE.Vault.Gain
/-!
# Boot installation, one shutter
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
attribute [local instance] Gauge.frobInner
variable {G:Gauge} (Y:Stage) {t:ℝ}
open YM.LocalLTE.Vault Animals
open Planned.GuardedAtom Guard Push Local
variable {n:Side} (R:Rep G n) {κ x τ:ℝ}(d c K:ℕ) (f:ℕ→ℕ) (w:Berths R.p R.activities (fun _:ℕ=> Animals.neighbors (terr G d+1) (0:Site n)))
    (Ψ:FrameBox.Grove (0:Site n))
    (n₀:ℕ)(he:1≤n₀)(hκ:Reliable G κ τ)(hb:∀ j,j≤K→ n₀ ≤ f j+1)
    (ht:Majesty G Y d c n₀ K κ x)(hX:2*(2*(terr G d+1))< n.val)
variable {σ C δ v v':ℝ}(hp:R.Lawful σ C v v' δ)(hv:0 < δ)(hd:Real.sqrt δ= Urns.divisor x)
    (hq :Time.Same Y R.p)(h' : R.p.B=radiusB x)(hz:R.p.threshold=temp x)
set_option quotPrecheck false
local notation "S"=> R.p
local notation "Z"=> Animals.neighbors (terr G d+1) (0:Site n)
local notation "u"=> (hullF Y c)
local notation "F"=> (Labels.frames G).level 0
variable {ι:Type} (P:ι→ℕ) (I:Finset ι)(k :∀ i:ι, ((Labels.frames G).level (P i)).Coeff)
    (H:∀ i∈I,P i ≤ d)(hB: I.card ≤ c)(hk:∀ i∈I, ((Labels.frames G).level (P i)).coeffSize (k i) ≤1)
    (hC:∀ z∈I,∀ i, R.p.Regular ((localSection G (P z)).footprint (0:Site n)) ((localSection G (P z)).places (Pi.single i 1) (0:Site n)) ∧ R.p.supBounds 0 ((localSection G (P z)).footprint (0:Site n)) ((localSection G (P z)).places (Pi.single i 1) (0:Site n)) (Y.columns*R.p.threshold^(((Labels.frames G).level (P z)).grades i).2))
local notation "Q"=> fareK R.p P k I (0:Site n)
local notation "W"=> draw F R (Z) Q w
local notation "β"=> culture Y c
local notation "Q'"=> (fun _:ℕ=> Vault.roughHat (Q-Vault.halcyon Q) Ψ F (terr G d) n₀ κ)
include hκ h' hq hp hv hX hd hz hB hk hC hb he ht H
-- true stamp plus projection cap. prices from REAL labels at 0.
set_option maxHeartbeats 600000 in
lemma cakeB (l:ℕ)(hℓ:terr G d+1≤ l): let D:= draw F R (Z) Q w; let ξ:=localSection G 0; D.Format 0 (hol G) R∧ (∀ U, D.density 0 ξ R U=(R.eval U:ℂ)*Q U) ∧ D.remBound 0 R (Real.sqrt δ) (culture Y c) ∧ ( (Labels.frames G).level 0).coeffSize D.x ≤ 1 ∧ LocalLTE.Concourse.Center ξ (hol G) R D Q' f K l κ (Real.sqrt δ) (fun _=>x) (weightC x) (weightC x):=by
    intro L A
    obtain ⟨h₁,hP,hY⟩:= hq
    have hY:= ht.budgets n R.p (by assumption) (by assumption) (by assumption) hz h'; dsimp only at hY
    obtain ⟨hx',hδ,hM,hV,hA⟩:= hY
    rw [← hd] at hx' hδ
    let Z₀:= neighbors (terr G d) (0:Site n)
    have hs:= Vault.fare_good (0:Site n) R.p P k I hk d H hC Y.columns_ge -- order
    have ht1: R.p.Regular (Z₀) (Q):= hs.1; have hb': R.p.Regular (Z₀) (Q-Vault.halcyon Q):= regular_sub ht1 (regular_const _); have hz0: ‖Q 1‖ ≤1:= Vault.fare_small R.p P k I hk
    have hc:0 ≤R.p.mass Z u:=by
       have hp :0≤ hullF Y c:=by unfold hullF Vault.froth; have hp:0≤Y.columns:=zero_le_one.trans Y.columns_ge; positivity
       exact hp.trans (R.p.loMass _ _ hp)
    have hθ: Z₀ ⊆ Z:=fun i hi'=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp hi').trans (Nat.le_succ _))
    let hΔ:= wideFare G d x c+1; let b0:= Q-Vault.halcyon Q; let r:= hitWidth R.p*δ*Local.reservedMass R.p Z hΔ
    have heV:0 ∈ Z:= (neighbors_mem ..).2 (by simp)
    have ht' : (R.p).threshold⁻¹ ≤x:=by rw [hz]; exact Doors.temp_cheap ht.β
    have hZ(v): ‖Q v-Q 1‖≤ wideFare G d x c+1:= (norm_sub_le ..).trans (add_le_add (Vault.wideB (o:=(0:Site n)) R.p P k I hk d H c hB ht.β ht' v) hz0) -- order
    have hp₀:R.p.supBounds 0 Z₀ b0 u:= by
        apply bound_weaken (bound_sub ht1 (regular_const (Q 1)) hs.2 (bound_const (Q 1)))
        apply add_le_add _ hz0; unfold Vault.froth; rw [show (R.p).order=Y.order from ?_]; exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) Y.columns_ge) hB; assumption -- bound_const function.ht
    obtain ⟨hf,he',hL,hs,hT⟩:=Vault.roots F R Z Q w heV hp hv (Dilation.usualPerm hx' hv|>.2) (regular_larger ht1 hθ) (hol G) A hZ u (bound_larger hp₀ hθ) -- args order
    have hΓ: R.p.mass Z u ≤ (Real.exp ((Y.supportExponent+2)*ballCost 1))*u:=by
       have hi:= Spool.cover_boot x (n:=n) (s:=terr G d) (o:=(0:Site n)) ht.tempo -- location
       have hβ : 0≤(R.p).supportExponent:= R.p.exponent_pos.le
       have hX' : R.p.supportExponent=Y.supportExponent:= by assumption
       apply mul_le_mul_of_nonneg_right _ hp₀.1; apply Real.exp_monotone; rw [h',hX']; exact mul_le_mul (le_add_of_nonneg_right zero_le_two) (by exact_mod_cast hi) (Nat.cast_nonneg _) (add_nonneg Y.price_pos.le zero_le_two)
    have heY:Real.sqrt δ>0:=Real.sqrt_pos.mpr hv
    have hV' : r ≤ Real.sqrt δ * weightC x K:=by refine le_trans ?_ (mul_le_mul_of_nonneg_left hδ heY.le); unfold r; nth_rw 1 [← Real.mul_self_sqrt hv.le]; apply le_of_eq; ring
    have Ht : r/Real.sqrt δ ≤ 1:=by
        apply le_trans ((div_le_iff₀ heY).2 (hV'.trans_eq (mul_comm ..))) _; exact Real.rpow_le_one_of_one_le_of_nonpos ht.β (bitN ..)
    refine ⟨hf,hL,hT.bound (add_le_add hΓ Ht), ?_, ⟨?_,?_,fun _ _ => rfl⟩⟩
    · rw [Concourse.center_size, show L.x 0 = _ from he']; exact hz0
    · intro j hj; let D:= Q'; let s₀:= x^(echoBit K-1); let C:= D j
      have hx₀ : weightC x K ≤ weightC x j:= Real.rpow_le_rpow_of_exponent_le ht.β (echo_antitone hj)
      have hs(i:Bool):R.p.supBounds 0 Z ((Port.scaleQ i ∘ b0)- (FrameBox.Hall.shave Ψ (terr G d) κ n₀ (Port.scaleQ i ∘ b0))) s₀:= hA (by omega) (by omega) ι P k I hB H hk Ψ ⟨hb',hp₀⟩ i
      have hι(i:Bool):ContDiffAt ℝ (↑ n₀) ((Port.scaleQ i∘b0)∘ FrameBox.Grove.soloV) 0:= (Vault.shades n₀ R.p P k I hk d c H hB ht.β ht' (0:Site n) i 0 (by simp)).smooth -- order check.
      change LocalLTE.River.Exhibition A κ l (f j) (hol G) R _ C (Real.sqrt δ) x _
      apply Vault.supported b0 Ψ hκ (hol G) A R hb' hp₀ (by exact sub_self _) L rfl rfl hf (v:=weightC x K) _ hs hι he l hℓ (f j) (hb j hj) (Real.rpow_nonneg (zero_le_one.trans ht.β) _) hx₀ hv (hM.trans hx₀) hV -- hT
      obtain ⟨c₀,hf',hz⟩:=hT.forced; exact ⟨_,⟨hf'.1,hf'.2.1,hf'.2.2.trans (by rw [mul_div_cancel₀ _ heY.ne']; exact hV')⟩,hz⟩
    intro j hj; let j0:=j; -- likely name.
    let s1:=Q' j; have h:s1.x=0:=rfl
    have hxL:0 ≤ weightC x j:= Real.rpow_nonneg (zero_le_one.trans ht.β) _
    refine ⟨?_, ⟨fun _=> 0,?_,?_⟩,?_⟩
    · exact (show _ from (by simpa [Vinca.decrement,Labels.Frame.coeffSize] using hxL))
    · simp only [BudgetPoint.mass,mul_zero]; exact Local.sumBudget_zero hxL
    · intro i; change River.Canvas A κ l (f _) R.p _ (s1.regular i - s1.regular i) 0; rw [sub_self]; exact River.Canvas.quiet le_rfl
    change s1.forced-s1.forced=0; rw [sub_self]
end YM.PhysicalNext.Repeat.Legato.Spool

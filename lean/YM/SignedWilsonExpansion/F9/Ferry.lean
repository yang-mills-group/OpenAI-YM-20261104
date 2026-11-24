import YM.SignedWilsonExpansion.F9.Reef

/-! # Finite profile stop price (adapted from WilsonIndependentRawRosterBudget/Orbit). Inductive
 joint product choices before approving the powers in the composite. Lantern through lamp depth. -/
set_option autoImplicit false
set_option maxHeartbeats 730000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.Reef
open Function Filter Finset Lattice Laurent Matrix Wilson RG Gauge Source Labels Exterior
open XSpace PertExtension.Series.Radial Blue Power Bank Soil FreeResolvent Cosmos Cosmos.Polestar Embroider Tree
open RegulatorIR RegulatorIR.Profiles RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Binding
open RegulatorIR.Diagram RegulatorIR.Prim RegulatorIR.Cluster RegulatorIR.Budget RegulatorIR.Budget.Packet
open PertExtension FVA2 Integration
open PowerSeries
open scoped Classical ENNReal NNReal Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{W I:Type}{n:Side}
namespace Ear
open RegulatorIR.Cluster.Collapsed
open RegulatorIR.Taping
open RegulatorIR.Motion
open Integration.WilsonIndependentRawWordGeometry
variable (Y : I→Pill G)
def tariffA : Composite I → ℕ → ℕ → ℕ → ℝ≥0∞
  | .atom i,u,j,r => markQ (root 0 u) (virtualP (Y i) j r)
  | .pair l a,u,j,r =>
    ∑ b ∈ (_root_.Finset.HasAntidiagonal.antidiagonal j : Finset (ℕ×ℕ)),
      ∑ c ∈ (_root_.Finset.HasAntidiagonal.antidiagonal r : Finset (ℕ×ℕ)),
        tariffA l u b.1 c.1 * tariffA a u b.2 c.2

def travel (J:Composite I)(x:Room)(o:I → Cover)(u:ℕ):ℝ≥0∞:=
  foldR (fun i=>displacement x (o i) u) J

def span (x:Room)(o:I → Cover):Composite I → ℝ
  | .atom i=>dist x (slide 1 (o i))
  | .pair l a=>span x o l + span x o a

theorem extent (x:Room)(o:I → Cover)(J:Composite I):0 ≤ span x o J:=by
  induction J with
  | atom _ => exact dist_nonneg
  | pair _ _ h h' => exact add_nonneg h h'

theorem housing (J:Composite I)(x:Room)(o:I → Cover)(u:ℕ):
    travel J x o u ≤ (ENNReal.ofReal (1+span x o J))^(J.accounts fun _=>u):=by
  induction J with
  | atom i => simp only [travel,foldR,span,Composite.accounts,displacement,Tariff.amount,div_one,le_refl]
  | pair l a hl ha =>
    change travel l x o u*travel a x o u ≤ _^(_+_)
    apply (mul_le_mul' hl ha).trans
    rw [pow_add]
    apply mul_le_mul' <;> apply pow_le_pow_left' <;> apply ENNReal.ofReal_le_ofReal
    · change 1+span x o l ≤ 1+(span x o l+span x o a)
      linarith [extent x o a]
    · change 1+span x o a ≤ 1+(span x o l+span x o a)
      linarith [extent x o l]

local notation "salary" => tariffA Y
theorem finite (J:Composite I):∀u j r,salary J u j r ≠ ⊤:=by
  induction J with
  | atom i =>
    intro u j r
    exact WilsonIndependentRawWordGeometry.finite _ _
      ((symbol_real (Y i)).choose_spec.1.canopy j r)
  | pair l a hl ha =>
    intro u j r
    unfold tariffA
    apply ENNReal.sum_ne_top.mpr
    intro b _
    apply ENNReal.sum_ne_top.mpr
    intro c _
    exact ENNReal.mul_ne_top (hl u b.1 c.1) (ha u b.2 c.2)

theorem district_bound (J:Composite I)(x:Room)(o:I → Cover)(u:ℕ):∀j r,
    markQ (district x u) (Reef.seed Y o J j r) ≤ salary J u j r*travel J x o u:=by
  induction J with
  | atom i =>
    intro j r
    exact recenter x u (virtualP (Y i) j r) (o i)
  | pair l a hl ha =>
    intro j r
    change markQ (district x u) (accord (seed Y o l) (seed Y o a) j r) ≤
      salary (.pair l a) u j r*(travel l x o u*travel a x o u)
    unfold accord tariffA
    apply (quota_sum ..).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    unfold crisp
    apply (quota_sum ..).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c hc
    rw [←_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hc,pie,dif_pos rfl]
    apply (packet_pair zero_lt_one u {x} (localL (G:=G) 1) _ _).trans
    apply (mul_le_mul' (hl b.1 c.1) (ha b.2 c.2)).trans_eq
    ring

theorem original (J:Composite I)(x:Room)(o:I → Cover)(u j r:ℕ):
    markQ (root x u) (Reef.seed Y o J j r) ≤
      salary J (u+u) j r*(ENNReal.ofReal (1+span x o J))^(J.accounts fun _=>u+u):=by
  exact (joined_root x u _).trans ((district_bound Y J x o (u+u) j r).trans
    (mul_le_mul_right (housing J x o (u+u)) _))


section
variable {M:I→ℕ}{n:Page M→Side}{S:Heir n G}
variable (V:Reel S)(x:I→Room)
include V in
theorem seated (start:∀ w,S.l (Page.opening M w)=1)(w:I)(u r:ℕ)(t:Packet (Foot G) r) :
    markQ (S.coverQ x u (Page.opening M w)) t = markQ (root (x w) u) t := by
  let s:=Page.opening M w
  change markQ ((Premium.rooted (Tariff.native (S.radius s) (S.radius_pos s) u) (x w)).uses
    (S.maps s).pos) t = _
  rw [V.realms]
  let fare (l:ℝ):= markQ ((Premium.rooted
    (Tariff.native (max 1 l) (lt_of_lt_of_le zero_lt_one (le_max_left ..)) u) (x w)).uses
    (localL l)) t
  change fare (S.l s)=_
  rw [show S.l s=1 from start w]
  have base (l:ℝ)(h:0<l)(he:l=1) : Tariff.native l h u=Tariff.native 1 zero_lt_one u := by
    subst l
    rfl
  exact congrArg (fun K:Tariff Room=>markQ ((Premium.rooted K (x w)).uses (localL 1)) t)
    (base _ _ (max_self (1:ℝ)))

end

section
open RegulatorIR.Ledger.Sky RegulatorIR.Budget.Layer
variable {J:Type}{M:J→ℕ}{n:Page M→Side}{S:Heir n G}(arms:Composite I)(T:S.Accounts)(sites:J→I → Cover)
def report:T.Report (arms.accounts (Pill.rank ∘ Y)):=
  declaring T (fun w=>seed Y (sites w) arms)
    (fun w=>(composed Y (sites w) arms).2)

theorem opening (V:Reel S)(L:Meter J)(x:J → Room)(p u:ℕ)
    (start:∀w,S.l (Page.opening M w)=1)
    (fare:∀w,ENNReal.ofReal (1+span (x w) (sites w) arms) ≤ L.val w):
    WilsonIndependentRawWordTransport.Opening (p:=p) (x:=x) (u:=u) (L:=L)
      (report Y arms T sites) (wage:=1):=by
  intro j _ r
  apply Carry.regular
  refine ⟨_,arms.accounts (fun _=>u+u),finite Y arms (u+u) j r,?_⟩
  intro w
  change markQ (S.coverQ x u (Page.opening M w)) (seed Y (sites w) arms j r) ≤ _
  rw [seated V x start w u r]
  apply (original Y arms (x w) (sites w) u j r).trans
  exact mul_le_mul_right (pow_le_pow_left' (fare w) _) _

variable {T}{V:Reel S}{Γ:Flap M → Layer (Foot G) (Foot G)}{B:Flap M → Bride G}
    {L:Meter J}{cash:Flap M → ℝ≥0∞}{p f u:ℕ}{D:Choice M}{γ c₀:ℝ}
    (A:Cylinder V T Γ B L cash p f u)(lamp:Lantern S D L cash γ)(endings:V.Endings L)
    (P:J → Period) (Q:∀w,(P w).Tree)(x:J → Room)
    (start:∀w,S.l (Page.opening M w)=1)(clock:∀w,V.clock (Page.opening M w)=Integration.WilsonIndependentMatchedOrbitReading.originalClock)
    (same:∀w,TopF n w=(P w).side)
    (fare:∀w,ENNReal.ofReal (1+span (x w) (sites w) arms) ≤ L.val w)
    (clear:0<c₀)(safe:S.cushion c₀ x)
include A lamp endings start clock same fare clear safe

theorem stopped (q:ℕ)(hq:q ≤ p)(stop:Choice M)(older:D.age ≤ stop.age):
    ∃ C:ℝ,∃ k:ℕ,0 ≤ C ∧ ∀ w,
      ‖PowerSeries.coeff q (Bare.normalized (Q w) G
        (Reef.main Y (sites w) (P w) (Q w) arms))-
        (note ((report Y arms T sites).main (stop.choose w) q 0):ℂ)‖ ≤
      C*(L.val w).toReal^k*S.modifyErr 0 f γ stop w:=by
  let Z:=report Y arms T sites
  let U:=fun w=>oblige Y (sites w) arms
  have seed:=opening Y arms T sites V L x p (u+f+f) start fare
  obtain ⟨C,k,hC,money⟩:=WilsonIndependentRawWordOrbit.numerical A Z U
    (fun w=>(composed Y (sites w) arms).1) lamp seed clear safe endings hq older
  refine ⟨C,k,hC,fun w=>?_⟩
  have hw:=money w
  rw [clock w,same w] at hw
  rw [landed Y (sites w) (P w) (Q w),←Complex.ofReal_sub,Complex.norm_real]
  exact hw

theorem terminal (q:ℕ)(hq:q ≤ p)(hi:γ<1)(last:ℕ)(sides:∀w,(n (Page.finallyW M w)).val ≤ last):
    ∃ C:ℝ,∃ k:ℕ,0 ≤ C ∧ ∀ w,
      ‖PowerSeries.coeff q (Bare.normalized (Q w) G
        (Reef.main Y (sites w) (P w) (Q w) arms))-
        (note ((report Y arms T sites).main (Page.finallyW M w) q 0):ℂ)‖ ≤
      C*(L.val w).toReal^k*(S.P w)^(-(γ/2)):=by
  obtain ⟨C,k,hC,price⟩:=stopped Y arms sites A lamp endings P Q x start clock same fare
    clear safe q hq (WilsonIndependentRawPeriodPower.terminal M) D.young
  let ck:=2+(last:ℝ)^γ
  have hk:0 ≤ ck:=by unfold ck; positivity
  refine ⟨C*ck,k,mul_nonneg hC hk,fun w=>?_⟩
  apply (price w).trans
  have bill:=WilsonIndependentRawPeriodPower.cost V γ lamp.gleams hi
    f last A.positive start sides w
  exact (mul_le_mul_of_nonneg_left bill (mul_nonneg hC (by positivity))).trans_eq (by unfold ck;ring)

end
end Ear
end YM.WilsonCoeffUV.Mer.Xa.Reef

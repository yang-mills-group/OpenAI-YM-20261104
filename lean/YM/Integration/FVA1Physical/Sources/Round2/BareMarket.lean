import YM.Integration.FVA1Physical.Sources.Round2.OrbitBarePrice
import YM.Integration.FVA1Physical.Wilson.CountableGate
import YM.RG01.Slack

/-! Every fixed marked bare comparison on one selected trajectory. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Lattice RG YM.Wilson Precision Tree Marker Comparison.RG02
open FVA2.CityHistory FormalOPE.RG10.InversionTop RGComparison.Core16 RGComparison.Core16.Parcel.Oven
open PhysicalNext.Repeat.Legato PertExtension.Series.Tested Pert.Asymptotics
open YM.Integration.FVA1Physical.Wilson YM.Qlocal.Schedule
open scoped Classical BigOperators Topology
variable {G : Gauge}

/-- A stage-specific version of the normalized weak-field comparison, quantified
over all spatial placements, chart choices and independently realized Wilson chains. -/
def BareAt {n : ℕ} (R : Census (Fin n)) (A : Run G) (m d r : ℕ) (Q η : ℝ) : Prop :=
  ∀ p : ℕ, let S:=A.family.path.levels.clock.op m p
  Bid.Larger (G:=G) S → ∀ (a : Fin n → CoverLabel G d) (s : R.Mode)
    (y : Fin n → Site (A.family.side (m+1) p)) (F : Forest S.ratio) (t : S.Choices)
    (u : Pins G (A.family.side m p)) (L : Bulk.Chain A.family.path), (∀ e, ‖u e‖ ≤ Q) →
    let W:=placeLabels (C:=A.family) a y; let g:=regulatorRun A.family (m+1) p (m+1)
    let x:=axesP G _ u; let co:=fun k=>(MSMatch.SourceTop.datum R m p W F t x).ordinaryCoefficient L r k s
    ‖(MSMatch.SourceTop.torusVacuum (C:=A.family) m p x g)⁻¹ • MSMatch.SourceTop.torusFull m p W x s.val g
      - peval co r g‖ ≤ g^((r:ℝ)+1-η)

private theorem localCeiling {n : ℕ} (R : Census (Fin n)) (hG : G.Simple) (d r q z : ℕ) :
    ∃ bill : Patch → KernelChoices → ℝ, ∀ (A : Run G) (m : ℕ),
    (∀ p, let S:=A.family.path.levels.clock.op m p
      bill S.patch S.kernel ≤ A.family.path.levels.clock.hatBeta m) →
    BareAt R A m d r ((q:ℝ)+1) (margin z) := by
  choose δ C hδ _ offer using static_bare_price (G:=G) R d r ((q:ℝ)+1) (by positivity)
  have afford (P K) : ∃ x : ℝ, ∀ β ≥ x, (δ P K)⁻¹ ^2 ≤ β ∧ 0<β ∧ C P K ≤ β^(margin z/2) := by
    apply eventually_atTop.1
    filter_upwards [eventually_ge_atTop ((δ P K)⁻¹^2),eventually_gt_atTop (0:ℝ),
      (tendsto_rpow_atTop (half_pos (margin_pos z))).eventually_ge_atTop (C P K)] with β small pos credit
    exact ⟨small,pos,credit⟩
  choose cost money using afford
  refine ⟨fun P K=>2*cost P K,?_⟩
  intro A m gate p S room a s y F t u L hu W g x co
  let θ:=A.family.path.levels.clock.hatBeta
  let β:=A.family.path.β (m+1) p (m+1)
  have lo : 2*cost S.patch S.kernel ≤ θ m:=gate p
  have mono : θ m ≤ θ (m+1):=WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos hG).le (Nat.le_succ m)
  have band : θ (m+1)/2 ≤ β:=(A.makes.wilson.represents (m+1) p (m+1) le_rfl).band.1
  obtain ⟨small,pos,credit⟩:=money S.patch S.kernel β (by linarith only [lo,mono,band])
  have hg : 0<g:=inv_pos.mpr (Real.sqrt_pos.mpr pos)
  have wid : g≤δ S.patch S.kernel := by
    change (Real.sqrt β)⁻¹ ≤ δ S.patch S.kernel
    have hs : (δ S.patch S.kernel)⁻¹≤Real.sqrt β := by
      simpa only [Real.sqrt_sq (inv_nonneg.mpr (hδ S.patch S.kernel).le)] using Real.sqrt_le_sqrt small
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hδ S.patch S.kernel)) hs
  have eqn : β^(margin z/2)=g^(-margin z) := by
    change β^(margin z/2)=((Real.sqrt β)⁻¹)^(-margin z)
    rw [Real.sqrt_eq_rpow,←Real.rpow_neg pos.le,←Real.rpow_mul pos.le];congr 1;ring
  apply (offer S.patch S.kernel a s A m p rfl rfl y F t u L room hu g hg wid).trans
  calc C S.patch S.kernel*g^(r+1) ≤ g^(-margin z)*g^(r+1) :=
        mul_le_mul_of_nonneg_right (credit.trans_eq eqn) (pow_nonneg hg.le _)
       _ = g^((r:ℝ)+1-margin z) := by
        rw [←Real.rpow_natCast g (r+1),←Real.rpow_add hg];congr 1;push_cast;ring

private structure BareRequest where
  count : ℕ
  batch : Census (Fin count)
  horizon : ℕ
  truncation : ℕ
  radius : ℕ
  loss : ℕ

private instance {n : ℕ} : Finite (Census (Fin n)) :=
  Finite.of_injective Census.choices (fun {x y} h=>by cases x;cases y;congr)

private instance : Countable BareRequest :=
  Function.Injective.countable (f:=fun k:BareRequest => (⟨k.count,k.batch,k.horizon,k.truncation,k.radius,k.loss⟩ :
    Σ n:ℕ, Census (Fin n) × ℕ × ℕ × ℕ × ℕ)) (by rintro ⟨a,b,c,d,e,f⟩ ⟨_,_,_,_,_,_⟩ h;cases h;rfl)

private noncomputable instance : Encodable BareRequest := Encodable.ofCountable BareRequest

/-- A single obtainable bill. On any trajectory that pays it, all fixed loads, finite
field horizons, truncation orders, bounded weak gauges and positive exponent losses
are available at all sufficiently late stages, uniformly in admitted periodic volume. -/
theorem every_bare_invoice (G : Gauge) (hG : G.Simple) :
    ∃ f : StageThreshold, Obtainable (selectedThreshold (G:=G) f) ∧ ∀ (A : Run G),
    selectedThreshold f A.metals A.rolls A.alloy A.kit →
    ∀ (n d r : ℕ) (R : Census (Fin n)) (Q η : ℝ), 0<η →
      ∀ᶠ m : ℕ in atTop, BareAt R A m d r Q η := by
  choose quote paid using fun i:BareRequest=>localCeiling i.batch hG i.horizon i.truncation i.radius i.loss
  let bill (i : ℕ) (P : Patch) (K : KernelChoices) := ((Encodable.decode (α:=BareRequest) i).map (fun x=>quote x P K)).getD 0
  let budget : StageThreshold:=fun lo _ P K=>∑ i ∈ Finset.range (lo.order+1), |bill i P K|
  refine ⟨budget,selectedThreshold_obtainable budget,?_⟩
  intro A invoice n d r R Q η positive
  obtain ⟨q,hq⟩:=exists_nat_ge Q
  obtain ⟨z,hz⟩:=margin_eventually positive
  let ask : BareRequest:=⟨n,R,d,r,q,z⟩
  let j:=Encodable.encode ask
  filter_upwards [eventually_ge_atTop (A.t j),
    (RG01.Physical.hats hG A.family.path.levels).eventually_ge_atTop (2:ℝ)] with m since later
  have rank : j ≤ (A.alloy.B.a.params m).order := (Nat.le_succ j).trans (((A.makes.stages j).2 m since).1)
  have charge (p : ℕ) : let S:=A.family.path.levels.clock.op m p
      quote ask S.patch S.kernel ≤ A.family.path.levels.clock.hatBeta m := by
    intro S
    have eq : bill j S.patch S.kernel=quote ask S.patch S.kernel := by simp [bill,j]
    have key : j ∈ Finset.range ((A.alloy.B.a.params m).order+1):=Finset.mem_range.mpr (Nat.lt_succ_of_le rank)
    have enrolled:=Finset.single_le_sum (f:=fun i=>|bill i S.patch S.kernel|) (fun i _=>abs_nonneg _) key
    calc quote ask S.patch S.kernel = bill j S.patch S.kernel := eq.symm
         _ ≤ |bill j S.patch S.kernel| := le_abs_self _
         _ ≤ _ := enrolled.trans (invoice m p)
  have score:=paid ask A m charge
  intro p S room a s y F t u L hu W g x co
  have raw:=score p room a s y F t u L (fun e=>(hu e).trans (hq.trans (by linarith : (q:ℝ)≤q+1)))
  let β:=A.family.path.β (m+1) p (m+1)
  have band : A.family.path.levels.clock.hatBeta (m+1)/2 ≤ β:=(A.makes.wilson.represents (m+1) p (m+1) le_rfl).band.1
  have mono := WilsonStartup.Timing.hat_mono A.family.path.levels (Gauge.slopeConstant_pos hG).le (Nat.le_succ m)
  have hb : 1≤β:=by linarith only [later,mono,band]
  have unit : g≤1:=(inv_le_one₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le hb))).2 (by simpa using Real.sqrt_le_sqrt hb)
  exact raw.trans (Real.rpow_le_rpow_of_exponent_ge (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hb))) unit
    (sub_le_sub_left hz ((r:ℝ)+1)))

end YM.Integration.FVA1Physical.Round2.Curvature

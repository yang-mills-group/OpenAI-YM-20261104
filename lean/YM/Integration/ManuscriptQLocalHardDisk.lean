import YM.Integration.ManuscriptQLocalExceptionalCounts
import YM.Integration.ManuscriptQLocalMarkedHeightTail

/-! An auxiliary complex variable multiplies each entire integrated hard component.
The same genuine pre-collapse root tariff pays all occupied hard components and
restores the physical radii of the external nilpotent marks once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHardDisk
open Filter Function Finset Lattice RG Tree Pressure Pressure.Stores ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Next.Scheduling AnalyticBridge VerifiedReset
open MergeProof Marker Extra.Multi LocalLTE PhysicalNext.Repeat.Daisy
open ManuscriptQLocalMarkedHeightTail
open scoped Classical Topology BigOperators

variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W x μ a:ℝ}
  {o:Target.Order G W} (H:Cash W x μ L Q o a T R)

theorem reserve (ℓ:ℕ) (hβ:1≤betaF G x L)
    (hc:Height.grow G L x^ℓ≤Real.exp (Q.mark L μ x)) (z:H.fragrances)
    {q:ℕ} (hq:q≤Height.overlap H z) : (Height.grow G L x^ℓ)^q≤Height.beaconN H ℓ z := by
  have hg:1≤Height.grow G L x:=Real.one_le_rpow hβ (by norm_num)
  have hq':(q:ℝ)≤Height.overlap H z:=by exact_mod_cast hq
  have he:1≤Real.exp (Q.ε*Height.depth H z):=Real.one_le_exp
    (mul_nonneg Q.usable.le (sum_nonneg fun i _=>H.positive_volume _))
  calc _≤Real.exp (Q.mark L μ x)^q:=pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans hg) _) hc _
       _=Real.exp (Q.mark L μ x*q):=by rw [mul_comm,Real.exp_nat_mul]
       _≤Real.exp (Q.mark L μ x*Height.overlap H z):=
         Real.exp_monotone (mul_le_mul_of_nonneg_left hq' H.laws.acquired.marked)
       _≤Height.beaconN H ℓ z:=(le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hg)).trans
         (le_mul_of_one_le_right (by positivity) he)

/-- Local height, occupied seeds, and true geometric depth contribute distinct
factors of the same original pre-collapse estimate. -/
theorem aggregate (ℓ:ℕ) (hβ:1≤betaF G x L)
    (hm:Height.grow G L x^ℓ≤Real.exp (Q.mark L μ x))
    (hv:Height.grow G L x^ℓ≤Real.exp (Q.ε*Pressure.Stores.till x))
    (z:H.fragrances) {q:ℕ} (bill:ManuscriptQLocalExceptionalCounts.Invoice H ℓ z q) :
    (Height.grow G L x^ℓ)^q≤Height.beaconN H ℓ z := by
  obtain ⟨p,s,v,partition,degree,overlap,depth⟩ := bill
  let D:=Height.grow G L x
  have hd:1≤D:=Real.one_le_rpow hβ (by norm_num)
  have hn:0≤D:=zero_le_one.trans hd
  have price:0≤D^ℓ:=pow_nonneg hn _
  have tall:(D^ℓ)^p≤D^Height.degreeN H ℓ z:=by rw [←pow_mul];exact pow_le_pow_right₀ hd degree
  have seeds:(D^ℓ)^s≤Real.exp (Q.mark L μ x*Height.overlap H z):=by
    calc _≤Real.exp (Q.mark L μ x)^s:=pow_le_pow_left₀ price hm _
         _=Real.exp (Q.mark L μ x*s):=by rw [mul_comm,Real.exp_nat_mul]
         _≤_:=Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast overlap) H.laws.acquired.marked)
  have meters:(D^ℓ)^v≤Real.exp (Q.ε*Height.depth H z):=by
    calc _≤Real.exp (Q.ε*Pressure.Stores.till x)^v:=pow_le_pow_left₀ price hv _
         _=Real.exp (Q.ε*((v:ℝ)*Pressure.Stores.till x)):=by rw [←Real.exp_nat_mul];congr 1;ring
         _≤_:=Real.exp_monotone (mul_le_mul_of_nonneg_left depth Q.usable.le)
  calc (D^ℓ)^q≤(D^ℓ)^(p+s+v):=pow_le_pow_right₀ (one_le_pow₀ hd) partition
       _=((D^ℓ)^p*(D^ℓ)^s)*(D^ℓ)^v:=by rw [pow_add,pow_add]
       _≤Height.beaconN H ℓ z:=mul_le_mul
         (mul_le_mul tall seeds (pow_nonneg price _) (pow_nonneg hn _)) meters
         (pow_nonneg price _) (mul_nonneg (pow_nonneg hn _) (Real.exp_pos _).le)

lemma restore {b z d:ℝ} (hb:1≤b) (hz:0≤z) {n m t:ℕ}
    (occ : n ≤ m) (one : 1 ≤ t) (paid:b^m*z≤d) : z^t*b^n≤d^t := by
  have recurs:b^m≤(b^m)^t:=by
    calc _=(b^m)^1:=(pow_one _).symm
         _≤_:=pow_le_pow_right₀ (one_le_pow₀ hb) one
  calc _≤z^t*(b^m)^t:=mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hb occ).trans recurs) (pow_nonneg hz _)
       _=(b^m*z)^t:=by rw [mul_pow,mul_comm]
       _≤d^t:=pow_le_pow_left₀ (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) hz) paid _

variable {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι] {Γ:Marker.Census V}
  (M:ι→Menu.Hat Γ R)

private abbrev leaves (M:ι→Menu.Hat Γ R) := fun i=>(M i).M

variable {C d rv s A v₁ y B e:ℝ} {j k:ℕ} {χ:Push.SectorMeasure.Chi}
  (N:Captain H j C d rv s A v₁ y B e k χ)

theorem financed (n ℓ order:ℕ) (w:V→ℝ) (hw:∀v,0<w v) (hβ:1≤betaF G x L)
    {ρ:ℝ} (hr:0≤ρ)
    (gate:((betaF G x L)^2)^Fintype.card V*ρ^order≤Height.grow G L x^ℓ)
    (degree:Fan.Stars H (leaves M)→ℕ)
    (located:∀ z,ManuscriptQLocalForcedClusters.alive H χ (leaves M) z→(Height.grow G L x^ℓ)^(degree z)≤Height.beaconN H ℓ z.1)
    {u γ:ℝ}
    (bill:Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*
        Height.markU N (leaves M) (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M i) w) z n) γ u) :
    Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ (leaves M) z then
        ρ^(order*degree z)*(Poly.price w (matrix H M z)*Captain.wife N z.1 (leaves M) z.2 n) else 0) γ u := by
  classical
  let β:=betaF G x L
  let b:=β^2
  let r:=fun i=>Menu.sumFee (M i) w
  let r':=fun i=>β^(-(2:ℝ))*r i
  have hb:1≤b:=one_le_pow₀ hβ
  have bp:0<b:=zero_lt_one.trans_le hb
  have eβ:β^(-(2:ℝ))=b⁻¹:=by rw [Real.rpow_neg (zero_le_one.trans hβ)];norm_num [b,β]
  have r0 i:0≤r i:=Menu.timed _ hw
  have r1 i:0≤r' i:=mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hβ) _) (r0 i)
  let S':=fun z=>Fan.wagesZ (leaves M) H χ ℓ k r' N (fun _=>1) n z
  have paid:Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x) S' γ u:=
    Fan.ticketsT (leaves M) H χ ℓ k r' r1 N (fun _=>1) (fun _=>le_rfl) hβ n γ u bill
  have raw (z:Fan.Stars H (leaves M)):0≤Captain.wife N z.1 (leaves M) z.2 n:=
    mul_nonneg (pow_nonneg (by unfold March.shiftG;positivity) _)
      (Captain.fareV N z.1 (leaves M) z.2)
  have major (z:Fan.Stars H (leaves M)):0≤S' z:=
    Fan.roaring (leaves M) H χ ℓ k r' r1 N (fun _=>1) (fun _=>le_rfl) n z hβ
  have atKey (z:Fan.Stars H (leaves M)) (sel:0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ (leaves M) z) :
      ρ^(order*degree z)*(Poly.price w (matrix H M z)*Captain.wife N z.1 (leaves M) z.2 n)≤S' z := by
    by_cases hZ:phase H M w z=0
    · rw [physical H M w hw,hZ,smul_zero,Poly.zero_price,zero_mul,mul_zero];exact major z
    have occ:=occupied H M z (fun v=>(M v.2.val).charge/(Menu.sumFee (M v.2.val) w:ℂ)) hZ
    let p:=Captain.pearl z.1 (leaves M) r z.2
    let h:=Captain.wife N z.1 (leaves M) z.2 n
    have hp:0≤p:=Fan.pearlsNN (leaves M) H r r0 z
    have hphase:Poly.price w (matrix H M z)≤p:=by
      rw [physical H M w hw,Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
      exact (mul_le_mul_of_nonneg_left (unit H M w hw z) hp).trans (le_of_eq (mul_one _))
    have ze:=Fan.belayed (leaves M) H χ ℓ k r' N (fun _=>1) (fun _=>le_rfl) hβ n
      (fun _=>1) r' (fun _=>le_rfl) (fun _=>one_mul _ |>.symm) r1 z |>.2.1
    have ex:=located z sel.2
    have cz:Captain.pearl z.1 (leaves M) r' z.2=(b⁻¹)^Fintype.card (Occ H M z)*p:=by
      rw [←eβ];exact pearl_scale H M r _ z
    have scaled:(Height.grow G L x^ℓ)^(degree z)*((b⁻¹)^Fintype.card (Occ H M z)*p*h)≤S' z:=by
      rw [←cz]
      exact (mul_le_mul_of_nonneg_right ex (mul_nonneg (Fan.pearlsNN (leaves M) H r' r1 z) (raw z))).trans ze
    have spending:ρ^(order*degree z)*b^Fintype.card (Occ H M z)≤(Height.grow G L x^ℓ)^(degree z):=by
      rw [pow_mul];exact restore hb (pow_nonneg hr _) occ sel.1 gate
    calc _≤ρ^(order*degree z)*(p*h):=mul_le_mul_of_nonneg_left
             (mul_le_mul_of_nonneg_right hphase (raw z)) (pow_nonneg hr _)
         _=(ρ^(order*degree z)*b^Fintype.card (Occ H M z))*((b⁻¹)^Fintype.card (Occ H M z)*p*h):=by
             rw [inv_pow];field_simp [ne_of_gt bp]
         _≤(Height.grow G L x^ℓ)^(degree z)*((b⁻¹)^Fintype.card (Occ H M z)*p*h):=
             mul_le_mul_of_nonneg_right spending (mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr bp.le) _) hp) (raw z))
         _≤S' z:=scaled
  intro site
  apply budget_mono (paid site)
  · intro z
    dsimp only
    split_ifs <;> first | exact le_rfl | exact mul_nonneg (mul_nonneg (pow_nonneg hr _) (mul_nonneg (Poly.nonnegative hw _) (raw z))) (Real.exp_pos _).le | simp
  · intro z
    by_cases hz:site∈Captain.reachability z.1
    · simp only [if_pos hz]
      by_cases hs:0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ (leaves M) z
      · rw [if_pos hs];exact mul_le_mul_of_nonneg_right (atKey z hs) (Real.exp_pos _).le
      · rw [if_neg hs,zero_mul];exact mul_nonneg (major z) (Real.exp_pos _).le
    · simp only [if_neg hz,le_refl]

theorem boosted (n ℓ order:ℕ) (w:V→ℝ) (hw:∀v,0<w v) (hβ:1≤betaF G x L)
    (hc:Height.grow G L x^ℓ≤Real.exp (Q.mark L μ x)) {ρ:ℝ} (hr:0≤ρ)
    (gate:((betaF G x L)^2)^Fintype.card V*ρ^order≤Height.grow G L x^ℓ)
    (degree:Fan.Stars H (leaves M)→ℕ)
    (located:∀ z,ManuscriptQLocalForcedClusters.alive H χ (leaves M) z→degree z≤Height.overlap H z.1)
    {u γ:ℝ}
    (bill:Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*
        Height.markU N (leaves M) (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M i) w) z n) γ u) :
    Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ (leaves M) z then
        ρ^(order*degree z)*(Poly.price w (matrix H M z)*Captain.wife N z.1 (leaves M) z.2 n) else 0) γ u :=
  financed H M N n ℓ order w hw hβ hr gate degree
    (fun z live=>reserve H ℓ hβ hc z.1 (located z live)) bill

/-- The complex variable acts after all integrations of one hard component. -/
def decorated (degree:Fan.Stars H (leaves M)→ℕ) (order:ℕ) (ζ:ℂ) (z:Fan.Stars H (leaves M)) : Poly Γ :=
  ζ^(order*degree z) • matrix H M z

omit [Fintype V] [Fintype ι] in
lemma decorated_price (degree:Fan.Stars H (leaves M)→ℕ) (order:ℕ) (ζ:ℂ) (w:V→ℝ) (z:Fan.Stars H (leaves M)) :
    Poly.price w (decorated H M degree order ζ z)=‖ζ‖^(order*degree z)*Poly.price w (matrix H M z) := by
  rw [decorated,Poly.adapted,norm_pow]

omit [Fintype V] [Fintype ι] in
lemma physical_point (degree:Fan.Stars H (leaves M)→ℕ) (order:ℕ) (z:Fan.Stars H (leaves M)) :
    decorated H M degree order 1 z=matrix H M z := by simp [decorated]

theorem disk (n ℓ order:ℕ) (w:V→ℝ) (hw:∀v,0<w v) (hβ:1≤betaF G x L)
    (hc:Height.grow G L x^ℓ≤Real.exp (Q.mark L μ x)) {ρ:ℝ}
    (gate:((betaF G x L)^2)^Fintype.card V*ρ^order≤Height.grow G L x^ℓ)
    (degree:Fan.Stars H (leaves M)→ℕ)
    (located:∀z,ManuscriptQLocalForcedClusters.alive H χ (leaves M) z→degree z≤Height.overlap H z.1)
    {u γ:ℝ}
    (bill:Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*
        Height.markU N (leaves M) (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M i) w) z n) γ u)
    (ζ:ℂ) (hz:‖ζ‖≤ρ) :
    Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ (leaves M) z then
        Poly.price w (decorated H M degree order ζ z)*Captain.wife N z.1 (leaves M) z.2 n else 0) γ u := by
  have cap:= (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg ζ) hz order)
    (pow_nonneg (sq_nonneg (betaF G x L)) (Fintype.card V))).trans gate
  simpa only [decorated_price,mul_assoc] using boosted H M N n ℓ order w hw hβ hc
    (norm_nonneg ζ) cap degree located bill

lemma birthday {β D price ρ:ℝ} (hD:0<D) (hρ:0≤ρ) (v h:ℕ)
    (recovery:(β^2)^v*D⁻¹≤price) (circle:ρ^h*price≤1) : (β^2)^v*ρ^h≤D := by
  have debit:(β^2)^v≤price*D:=(div_le_iff₀ hD).mp (by simpa only [div_eq_mul_inv] using recovery)
  calc _≤(price*D)*ρ^h:=mul_le_mul_of_nonneg_right debit (pow_nonneg hρ _)
       _=(ρ^h*price)*D:=by ring
       _≤1*D:=mul_le_mul_of_nonneg_right circle hD.le
       _=D:=one_mul _

lemma physical_radius {g:ℝ} (hg:0<g) (h:ℕ) : (2*g)⁻¹^h*(2*g)^h≤1 := by
  rw [←mul_pow,inv_mul_cancel₀ (mul_pos (by norm_num) hg).ne',one_pow]

end YM.Integration.ManuscriptQLocalHardDisk

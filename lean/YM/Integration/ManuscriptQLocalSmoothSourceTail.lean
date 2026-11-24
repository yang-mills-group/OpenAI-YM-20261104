import YM.Integration.ManuscriptQLocalHardGraded
import YM.Integration.ManuscriptQLocalMarkedHeightRun

/-! All genuine smooth source occupations on the full integrated star, with its exact external marker restoration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalSmoothSourceTail
open Filter Function Finset Lattice RG Tree Pressure Pressure.Stores ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Next.Scheduling AnalyticBridge VerifiedReset
open MergeProof Marker Extra.Multi LocalLTE PhysicalNext.Repeat.Daisy
open ManuscriptQLocalMarkedHeightTail
open scoped Classical Topology BigOperators

variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W x μ a:ℝ}
  {o:Target.Order G W} (H:Cash W x μ L Q o a T R)

variable {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι] {Γ:Marker.Census V}
  (M:ι→Menu.Hat Γ R)

private abbrev leaves (M:ι→Menu.Hat Γ R) := fun i=>(M i).M

variable {C d rv s A v₁ y B e:ℝ} {j k:ℕ} {χ:Push.SectorMeasure.Chi}
  (N:Captain H j C d rv s A v₁ y B e k χ)

theorem funded (n ℓ:ℕ) (w:V→ℝ) (hw:∀v,0<w v) (hβ:1≤betaF G x L) {u γ:ℝ}
    (bill:Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*
        Height.markU N (leaves M) (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M i) w) z n) γ u) :
    Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>Poly.price w (matrix H M z)*Captain.wife N z.1 (leaves M) z.2 n) γ ((((betaF G x L)^2)^Fintype.card V)*u) := by
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
  have scaled:=Quotes.hit_scale (pow_nonneg (zero_le_one.trans hb) (Fintype.card V)) paid
  apply ManuscriptQLocalHardGraded.price_le scaled
  · intro z;exact mul_nonneg (Poly.nonnegative hw _) (raw z)
  intro z
  by_cases hZ:phase H M w z=0
  · rw [physical H M w hw,hZ,smul_zero,Poly.zero_price,zero_mul];exact mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) (major z)
  have occ:=occupied H M z (fun v=>(M v.2.val).charge/(Menu.sumFee (M v.2.val) w:ℂ)) hZ
  let p:=Captain.pearl z.1 (leaves M) r z.2
  let h:=Captain.wife N z.1 (leaves M) z.2 n
  have hp:0≤p:=Fan.pearlsNN (leaves M) H r r0 z
  have scalar:Poly.price w (matrix H M z)≤p:=by
    rw [physical H M w hw,Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
    exact (mul_le_mul_of_nonneg_left (unit H M w hw z) hp).trans (le_of_eq (mul_one _))
  have ze:=Fan.belayed (leaves M) H χ ℓ k r' N (fun _=>1) (fun _=>le_rfl) hβ n
    (fun _=>1) r' (fun _=>le_rfl) (fun _=>one_mul _ |>.symm) r1 z |>.2.1
  have cz:Captain.pearl z.1 (leaves M) r' z.2=(b⁻¹)^Fintype.card (Occ H M z)*p:=by
    rw [←eβ];exact pearl_scale H M r _ z
  have localPay:(b⁻¹)^Fintype.card (Occ H M z)*p*h≤S' z:=by
    rw [←cz];exact (le_mul_of_one_le_left (mul_nonneg (Fan.pearlsNN (leaves M) H r' r1 z) (raw z)) (Fan.bloomT (leaves M) H ℓ hβ z)).trans ze
  calc _ ≤ p*h:=mul_le_mul_of_nonneg_right scalar (raw z)
       _ = b^Fintype.card (Occ H M z)*((b⁻¹)^Fintype.card (Occ H M z)*p*h):=by rw [inv_pow];field_simp [bp.ne']
       _ ≤ b^Fintype.card (Occ H M z)*S' z:=mul_le_mul_of_nonneg_left localPay (pow_nonneg bp.le _)
       _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb occ) (major z)

/-- Every original source grade in the full star, whether or not it contains a protected member. -/
theorem deep (n ℓ cut:ℕ) (w:V→ℝ) (hw:∀v,0<w v) (hβ:1≤betaF G x L)
    (ν:ι→ℕ) {ρ:ℝ} (hr:1≤ρ) {u γ:ℝ}
    (bill:Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*Height.markU N (leaves M)
        (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (Menu.gradedHat (M i) ρ (ν i)) w) z n) γ u) :
    Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if cut≤ManuscriptQLocalHardGraded.ordinary H M ν z then
        Poly.price w (matrix H M z)*Captain.wife N z.1 (leaves M) z.2 n else 0) γ
      ((ρ^cut)⁻¹*((((betaF G x L)^2)^Fintype.card V)*u)) := by
  have sale:=funded H (fun i=>Menu.gradedHat (M i) ρ (ν i)) N n ℓ w hw hβ bill
  have hr₀:=zero_le_one.trans hr
  apply ManuscriptQLocalHardGraded.leftover hr (ManuscriptQLocalHardGraded.ordinary H M ν)
  · intro z
    exact mul_nonneg (Poly.nonnegative hw _) (mul_nonneg (pow_nonneg (by unfold March.shiftG;positivity) _) (Captain.fareV N z.1 (leaves M) z.2))
  · have same : Ac.Hit (fun z : Fan.Stars H (leaves M) => Captain.reachability z.1) (radiusB x)
        (fun z => Poly.price w (matrix H (fun i => Menu.gradedHat (M i) ρ (ν i)) z) *
          Captain.wife N z.1 (leaves M) z.2 n) γ ((((betaF G x L)^2)^Fintype.card V)*u) := sale
    simpa only [ManuscriptQLocalHardGraded.price_real H M ν hr₀ w,mul_assoc] using same

lemma numerical {β g:ℝ} (hg:0<g) (hβ:1≤β) (comparison:g≤2*(Real.sqrt β)⁻¹) (h v:ℕ) :
    (((2*g)⁻¹)^(h+4*v))⁻¹*((β^2)^v)≤(16:ℝ)^v*2^(h+4*v)*g^h := by
  have b:0<β:=zero_lt_one.trans_le hβ
  have s:0<Real.sqrt β:=Real.sqrt_pos.2 b
  have size:g*Real.sqrt β≤2:=(le_div_iff₀ s).1 (by simpa [div_eq_mul_inv] using comparison)
  have cap:β*g^2≤4:=by
    have z:=pow_le_pow_left₀ (mul_nonneg hg.le s.le) size 2
    rw [mul_pow,Real.sq_sqrt b.le] at z;nlinarith only [z]
  have four:β^2*g^4≤16:=by
    calc _ = (β*g^2)^2:=by ring
         _ ≤ (4:ℝ)^2:=pow_le_pow_left₀ (mul_nonneg b.le (sq_nonneg _)) cap 2
         _ = _:=by norm_num
  rw [inv_pow,inv_inv]
  calc _ = (2:ℝ)^(h+4*v)*g^h*(β^2*g^4)^v:=by
            rw [mul_pow (2:ℝ) g, pow_add g, pow_mul g, mul_pow (β^2) (g^4)];ring
       _ ≤ (2:ℝ)^(h+4*v)*g^h*(16:ℝ)^v:=mul_le_mul_of_nonneg_left
         (pow_le_pow_left₀ (by positivity) four _) (by positivity)
       _ = _:=by ring
end YM.Integration.ManuscriptQLocalSmoothSourceTail

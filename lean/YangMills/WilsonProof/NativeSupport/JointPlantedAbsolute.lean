import YangMills.WilsonProof.NativeSupport.JointOriginalResponse
import YangMills.WilsonProof.NativeSupport.JointRosterExtraction
import YangMills.WilsonProof.NativeSupport.JointPhysicalPrice

/-! Absolute, volume-independent interior bond susceptibility of the actual
planted roster at the original frozen inlet. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 165000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Next.Foundations Labels
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder WilsonUniformUnmarkedInletConnectedShift Dated
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {C:Campaign R} {Θ:Luna.Tableau C.width 300} {v:ℕ→ℕ→ℝ}
local notation "A₀" => R.alloy.B.a

theorem planted_absolute (sky:Campaign.Sky R C Θ v) (simple:G.Simple)
    (slow:∀ n,(((A₀).S.block n).val:ℝ) ≤ Real.log (2+Real.log ((A₀).clock.hatBeta n)))
    (support:∀ j,(((A₀).budget j).supportExponent+1)*((((A₀).S.block (j-1)).val:ℝ)^4) ≤ Real.sqrt ((A₀).clock.hatBeta j))
    (a:Roster G) (s:Finset (Fin a.length)) (hs:s.Nonempty) (radius W:ℕ)
    (stencils:∀ i:↥s,minSide G (grades a s i) ≤ radius):
    let m:=s.card
    let v₀:ℕ:=(2*radius+1)^4
    let ν:=tariffDegree Θ.price
    let d₀:=radiusDegree W v₀ ν
    let loss:=susceptibilityLoss m W v₀ ν
    ∀ᶠ k:ℕ in atTop,∀ u t,k ≤ t → ∀ tn:t < u+1,
      ((u+1-t:ℕ):ℝ)*Real.log 3 ≤ R.family.S.scale (u+1)-R.family.S.scale t →
      R.family.S.scale (u+1)-R.family.S.scale t ≤ (W:ℝ)*Real.log ((A₀).clock.hatBeta (u+1)) →
      ∀ per (T:Slices (A₀) per) (o:Fin a.length → Site (R.family.side (u+1) per)) i,i∈s →
      ∀ (z e:Site (R.family.side (u+1) per)) (part:Bool) (p:ℕ) (β δ:ℕ→ℝ) (r:ℝ),
        2*(2*d₀+1) ≤ p →
        let d:=traversal T tn.le
        let B:=line R.family.path per t (u+1)
        let Y:=temperatures β δ r
        let g:=regulatorRun R.family (u+1) per (u+1)
        let φ:=WilsonReportFrozenTraversal.planted R a s o i z e part
        Y d.depth=B d.depth →
        (∀ l,0 < l → l < d.depth → |Y l-B l| ≤ g^p) →
        (∑ q∈interior d,|picture d β δ 1 φ r q|) ≤
          2*5^m*bill (grades a s) G*(4^(2*d₀*(m+1))/g^loss) := by
  intro m v₀ ν d₀ loss
  letI:Nonempty ↥s:=hs.to_subtype
  filter_upwards [original_response (I:=↥s) sky simple slow (A₀).S.block_large support radius W] with k purchase
  intro u t kt tn lower upper per T o i hi z e part p β δ r order d B Y g φ endY near
  let x:ℝ:=height R (u+1)
  let h:=((x^d₀)⁻¹)^2
  let fee:ℝ:=4^(2*d₀*(m+1))/g^loss
  have xp:0 < x:=(zero_lt_one.trans ((A₀).fits.delayed (u+1))).trans_le (Nat.le_ceil _)
  let w (loc:↥s → Site (R.family.side (u+1) per)):=wordAt (grades a s) (labels a s) loc part
  have wc (loc):Continuous (w loc):=(component part).continuous.comp (continuous_finsetProd _ fun j _=>(localSection G (grades a s j)).continuous_places _ _)
  have wg (loc):GaugeInvariant (w loc):=by
    intro U X
    apply congrArg (component part)
    exact prod_congr rfl fun j _=>(localSection G (grades a s j)).placed_invariant (sound G _) _ _ U X
  have price (loc):(∑ q∈interior d,|picture d β δ 1 (w loc) r q|) ≤
      2^m*bill (grades a s) G*((5/2:ℝ)^m*fee) := by
    apply (word_picture d (traversal_ok T tn.le) β δ r (grades a s) (labels a s) loc part radius stencils _).trans_eq
    · rw [Fintype.card_coe]
    · intro F ct sym unit localF
      obtain ⟨hp,band,each⟩:=purchase t (u+1) kt tn lower upper per T loc F localF sym ct unit p β δ r order endY near
      have fixed:=roster_extraction d (traversal_ok T tn.le) β δ r 1 F ct sym hp each
      rw [Fintype.card_coe] at fixed
      have invoiced:(h^(m+1))⁻¹ ≤ fee:=terminal_price m W v₀ ν xp band
      exact fixed.trans (by rw [div_eq_mul_inv];exact mul_le_mul_of_nonneg_left invoiced (by positivity))
  let loc (x:Site (R.family.side (u+1) per)) (j:↥s):=Function.update o i x j.val
  change (∑ q∈interior d,|picture d β δ 1 (WilsonReportFrozenTraversal.planted R a s o i z e part) r q|) ≤ _
  rw [actual_planted R a s o i hi z e part]
  have total: (2:ℝ)^m*(5/2:ℝ)^m=5^m:=by rw [←mul_pow];norm_num
  calc
    _ ≤ _ := difference_picture d (traversal_ok T tn.le) β δ r (w (loc z)) (w (loc e)) (wc _) (wc _) (wg _) (wg _)
    _ ≤ _ := add_le_add (price (loc z)) (price (loc e))
    _ = _ := by rw [←total];dsimp only [fee];ring

end YM.Integration.InletSusceptibility.Packet

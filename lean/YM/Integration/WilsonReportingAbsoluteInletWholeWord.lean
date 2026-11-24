import YangMills.WilsonProof.NativeSupport.JointPlantedAbsolute
import YM.Integration.WilsonReportingAbsoluteInletCaptured

/-! The original absolute susceptibility of an un-subtracted, fixed-placement
Wilson roster. All marks, quiet deposits and the measured denominator share
the single physical history at the held identity. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 165000
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletWholeWord
open InletSusceptibility.Packet
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Next.Foundations Labels
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder WilsonUniformUnmarkedInletConnectedShift
open InletSusceptibility.Dated
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {C:Campaign R} {Θ:Luna.Tableau C.width 300} {v:ℕ→ℕ→ℝ}
local notation "A₀" => R.alloy.B.a

theorem susceptibility (sky:Campaign.Sky R C Θ v) (simple:G.Simple)
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
      ∀ per (T:Slices (A₀) per) (o:↥s → Site (R.family.side (u+1) per)) (part:Bool) (p:ℕ) (β δ:ℕ→ℝ) (r:ℝ),
        2*(2*d₀+1) ≤ p →
        let d:=traversal T tn.le
        let B:=line R.family.path per t (u+1)
        let Y:=temperatures β δ r
        let g:=regulatorRun R.family (u+1) per (u+1)
        let φ:=wordAt (grades a s) (labels a s) o part
        Y d.depth=B d.depth →
        (∀ l,0 < l → l < d.depth → |Y l-B l| ≤ g^p) →
        (∑ q∈interior d,|picture d β δ 1 φ r q|) ≤
          5^m*bill (grades a s) G*(4^(2*d₀*(m+1))/g^loss) := by
  intro m v₀ ν d₀ loss
  letI:Nonempty ↥s:=hs.to_subtype
  filter_upwards [original_response (I:=↥s) sky simple slow (A₀).S.block_large support radius W] with k purchase
  intro u t kt tn lower upper per T o part p β δ r order d B Y g φ endY near
  let x:ℝ:=height R (u+1)
  let h:=((x^d₀)⁻¹)^2
  let fee:ℝ:=4^(2*d₀*(m+1))/g^loss
  have xp:0 < x:=(zero_lt_one.trans ((A₀).fits.delayed (u+1))).trans_le (Nat.le_ceil _)
  let w (loc:↥s → Site (R.family.side (u+1) per)):=wordAt (grades a s) (labels a s) loc part
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
  have total : (2:ℝ)^m*(5/2:ℝ)^m=5^m := by rw [←mul_pow]; norm_num
  apply (price o).trans_eq
  rw [←total]
  ring

theorem replacement (sky:Campaign.Sky R C Θ v) (simple:G.Simple)
    (slow:∀ n,(((A₀).S.block n).val:ℝ)≤Real.log (2+Real.log ((A₀).clock.hatBeta n)))
    (support:∀ j,(((A₀).budget j).supportExponent+1)*(((A₀).S.block (j-1)).val:ℝ)^4≤Real.sqrt ((A₀).clock.hatBeta j))
    (a:Roster G) (s:Finset (Fin a.length)) (hs:s.Nonempty) (radius W:ℕ)
    (stencils:∀i:↥s,minSide G (grades a s i)≤radius):
    let S:ℕ:=(2*radius+1)^4
    let J:=radiusDegree W S (tariffDegree Θ.price)
    let H:=susceptibilityLoss s.card W S (tariffDegree Θ.price)
    let K:ℝ:=5^s.card*bill (grades a s) G*4^(2*J*(s.card+1))
    ∀ᶠ k:ℕ in atTop,∀u t,k≤t → ∀tn:t<u+1,
      ((u+1-t:ℕ):ℝ)*Real.log 3≤R.family.S.scale (u+1)-R.family.S.scale t →
      R.family.S.scale (u+1)-R.family.S.scale t≤(W:ℝ)*Real.log ((A₀).clock.hatBeta (u+1)) →
      ∀ per (T:Slices (A₀) per) (o:↥s→Site (R.family.side (u+1) per)) (part:Bool) (p:ℕ) (β δ:ℕ→ℝ) (η:ℝ),
        η≤1 → 2*(2*J+1)≤p →
        let d:=traversal T tn.le
        let B:=RGComparison.Core16.line R.family.path per t (u+1)
        let g:=regulatorRun R.family (u+1) per (u+1)
        let φ:=wordAt (grades a s) (labels a s) o part
        β+δ=B → δ d.depth=0 → (∀l,l≤d.depth → |δ l|≤η*g^p) →
        (∀r∈Set.Icc (0:ℝ) 1,(∑j∈interior d,|picture d β δ 1 φ r j|)≤K/g^H) ∧
        ∃r∈Set.Ioo (0:ℝ) 1,d.conditioned B φ 1-d.conditioned β φ 1=
            ∑j∈interior d,δ (lag d j)*picture d β δ 1 φ r j ∧
          |d.conditioned B φ 1-d.conditioned β φ 1|≤η*g^p*(K/g^H):=by
  intro S J H K
  filter_upwards [susceptibility sky simple slow support a s hs radius W stencils] with k paid
  intro u t kt tn floor roof per T o part p β δ η small order d B g φ endB endδ band
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cash:0≤η*g^p:=(abs_nonneg _).trans (band _ le_rfl)
  have line(l:ℕ):β l+δ l=B l:=congrFun endB l
  have all(r:ℝ)(hr:r∈Set.Icc (0:ℝ) 1):(∑j∈interior d,|picture d β δ 1 φ r j|)≤K/g^H:=by
    let Y:=temperatures β δ r
    have changeAt(l:ℕ):Y l-B l=(r-1)*δ l:=by rw [←line];change β l+r*δ l-(β l+δ l)=_;ring
    have terminal:Y d.depth=B d.depth:=sub_eq_zero.mp (by rw [changeAt,endδ,mul_zero])
    have charged(l:ℕ)(_lo:0<l)(lt:l<d.depth):|Y l-B l|≤g^p:=by
      rw [changeAt,abs_mul]
      have ur:|r-1|≤1:=abs_le.mpr ⟨by linarith only [hr.1],by linarith only [hr.2]⟩
      calc
        _≤1*|δ l|:=mul_le_mul_of_nonneg_right ur (abs_nonneg _)
        _≤1*(η*g^p):=mul_le_mul_of_nonneg_left (band l lt.le) zero_le_one
        _≤g^p:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right small (pow_nonneg gp p)
    have bought:=paid u t kt tn floor roof per T o part p β δ r order terminal charged
    simpa only [K,J,S,H,div_eq_mul_inv,mul_assoc] using bought
  let w (loc:↥s→Site (R.family.side (u+1) per)):=wordAt (grades a s) (labels a s) loc part
  have wc(loc):Continuous (w loc):=(component part).continuous.comp
    (continuous_finsetProd _ fun j _=>(localSection G (grades a s j)).continuous_places _ _)
  have wg(loc):GaugeInvariant (w loc):=by
    intro U X
    apply congrArg (component part)
    exact prod_congr rfl fun j _=>(localSection G (grades a s j)).placed_invariant (sound G _) _ _ U X
  have continuous : Continuous φ := wc o
  have gauge : GaugeInvariant φ := wg o
  obtain ⟨r,hr,eq⟩:=shift d (traversal_ok T tn.le) β δ 1 continuous gauge
  rw [endB] at eq
  have total:=eq.trans (WilsonUniformUnmarkedInletBondCovariances.centered d (traversal_ok T tn.le) β δ endδ 1 continuous r)
  refine ⟨all,r,hr,total,?_⟩
  rw [total]
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  calc
    _≤∑j∈interior d,η*g^p*|picture d β δ 1 φ r j|:=Finset.sum_le_sum fun j _=>by
      rw [abs_mul];exact mul_le_mul_of_nonneg_right (band (lag d j) (dates d j).1) (abs_nonneg _)
    _=η*g^p*(∑j∈interior d,|picture d β δ 1 φ r j|):=(Finset.mul_sum ..).symm
    _≤η*g^p*(K/g^H):=mul_le_mul_of_nonneg_left (all r ⟨hr.1.le,hr.2.le⟩) cash

open WilsonReportingAbsoluteInletNativeDates WilsonReportingAbsoluteInletNativeCoordinates
open WilsonReportingAbsoluteInletNativeInvoice WilsonReportingAbsoluteInletCaptured

def Receipt (R : Run G) (c : ℝ) (P q : ℕ) (b : Roster G) (h : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε →
    ∀ᶠ k : ℕ in atTop, ∀ s : Finset (Fin b.length), s.Nonempty →
      ∀ u, ultraviolet R.family c k ≤ u →
        let t := inlet R P u
        let N := u+1
        ∃ tu : t ≤ u, ∀ per, ∀ T : Slices R.family.path.levels per,
          ∀ (o : ↥s → Site (R.family.side N per)) (part : Bool),
            let d := traversal T (tu.trans u.le_succ)
            let g := regulatorRun R.family N per N
            let β := Descent.offset (finite R N per t (h N per)) g
            let φ := wordAt (grades b s) (labels b s) o part
            |WilsonReportingAbsoluteInletGust.physical R (tu.trans u.le_succ) φ 1 -
              d.conditioned β φ 1| / g^engineering b s ≤ ε*g^q

theorem reported (sky : Campaign.Sky R C Θ v) (simple : G.Simple) (slow : Pace R)
    (support : ∀ j, (((A₀).budget j).supportExponent+1)*
      (((A₀).S.block (j-1)).val:ℝ)^4 ≤ Real.sqrt ((A₀).clock.hatBeta j))
    {c : ℝ} (hc : 1 < c) (P q : ℕ) (b : Roster G) (h : ℕ → ℕ → ℕ → ℝ)
    (fund : InversePrice R (rank Θ.price P q b) h) :
    Receipt R c P q b h := by
  intro ε ep
  apply eventually_all.2
  intro s
  by_cases hs : s.Nonempty
  · let p := rank Θ.price P q b
    let K : ℝ := 5^s.card * bill (grades b s) G * 4^(2*degree Θ.price P b s*(s.card+1))
    let ε₀ := min ε 1
    let η := ε₀/(1+|K|)
    have pos : 0 < (1:ℝ)+|K| := by positivity
    have ep₀ : 0 < ε₀ := lt_min ep zero_lt_one
    have eta : 0 < η := div_pos ep₀ pos
    have small : η ≤ 1 := (div_le_one pos).2 ((min_le_right ε 1).trans (by linarith only [abs_nonneg K]))
    have win := Finset.le_sup
      (f:=fun t:Finset (Fin b.length)=>engineering b t+loss Θ.price P b t) (Finset.mem_univ s)
    have order : q+engineering b s+loss Θ.price P b s ≤ p := by dsimp [p,rank]; omega
    have gate : 2*(2*degree Θ.price P b s+1) ≤ p := (threshold Θ.price P b s hs).trans (by omega)
    have atoms (j : ↥s) : minSide G (grades b s j) ≤ extent b s :=
      Finset.le_sup (f:=fun j:↥s=>minSide G (grades b s j)) (Finset.mem_univ j)
    filter_upwards [replacement sky simple slow support b s hs (extent b s) (span P) atoms,
      WilsonReportingAbsoluteInletNativeInvoice.paid R simple slow hc P p h fund eta]
      with k prices date _ u front t N
    obtain ⟨tu,kt,low,high,windows⟩ := date u front
    refine ⟨tu,?_⟩
    intro per T o part d g β φ
    have measured := windows per T
    have paid := prices u t kt (Nat.lt_succ_of_le tu) low high per T o part p β
      (shifts R per t N - finite R N per t (h N per)) η small gate
      measured.2.2.1 measured.2.2.2.1 measured.2.2.2.2
    obtain ⟨_,_,_,_,fee⟩ := paid
    have signed : |WilsonReportingAbsoluteInletGust.physical R (tu.trans u.le_succ) φ 1 -
        d.conditioned β φ 1| ≤ (ε₀/(1+|K|))*g^p*(K/g^loss Θ.price P b s) := by
      rw [WilsonReportingAbsoluteInletGust.original R T (tu.trans u.le_succ) φ 1]
      exact fee
    exact (WilsonReportingAbsoluteInletPower.paid measured.1 measured.2.1 ep₀ order signed).trans
      (mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg measured.1.le _))
  · exact Eventually.of_forall (fun _ good => (hs good).elim)

end YM.Integration.WilsonReportingAbsoluteInletWholeWord

import YM.Integration.WilsonCapturedPrimarySubcellOrigin
import YM.Integration.WilsonCapturedPrimaryReflectedGeometry
import YM.Integration.WilsonCapturedPrimarySeparatedStop
import YM.Integration.WilsonCenteredCompactBooking

/-! The compact physical source on the original reflected cells at any fixed arity.
Its counterterm center belongs to each submitted support independently of its children. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPhysicalArray
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Extraction
open Extra.Histories Motion PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open Next.Rank WilsonReflectedMicroscopicSites
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {n N per J b:ℕ} (simple:G.Simple)
local notation "CF" => R.family
local notation "BB" i:max => ((CF).path.levels.budget i).B
local notation "copy" J:max per:max => Site ((CF).side J per)
local notation "centerOf" p:max J:max i:max => Mix.camp (CF) p J i
local notation "seen" r:max N:max p:max => WilsonCenteredCompactBooking.site R r (N,p)

def registered {l:ℕ} {f:Side} (z:Fin l → Site f) (root:Option (Fin l)) (u:Fin l) : Site f :=
  z u-root.elim 0 z

private theorem supported (φ:Test n) (r:ℝ) (z:Fin n→Site ((CF).side N per))
    (nz:WilsonCenteredCompactBooking.mass R φ r (N,per) z ≠ 0) :
    ∃x∈tsupport (fun y=>φ y),(seen r N per) x=z :=by
  by_contra! no
  apply nz
  change (∫x in WilsonCenteredCompactBooking.cell R r (N,per) z,φ x)=0
  have zero : Set.EqOn (fun x=>φ x) (fun _=>0) (WilsonCenteredCompactBooking.cell R r (N,per) z) :=by
    intro x hx
    by_contra ne
    exact no x (subset_closure ne) hx
  rw [setIntegral_congr_fun (WilsonCenteredCompactBooking.measurable_cell R r (N,per) z) zero]
  simp

/-- Every submitted child's actual reflected image and the distinct center
share one connected B-ball. The same witness works after deleting any faces. -/
theorem house (z:Fin n→Site ((CF).side N per)) (jb:J ≤ b) (live:b ≤ N)
    (home:∀v,separation (((CF).S.toDepth live per).parent (z v)) 0 ≤ BB b)
    (u:copy J per) (s:Finset (Fin n)) :
    coverNumber (BB b) (insert ((centerOf per J b) u)
      (s.image fun v=>site R (J:=J) z b (u,v))) ≤ 1 :=by
  let e:=(centerOf per J b) u
  suffices paid : covers (BB b) (insert e (s.image fun v=>site R (J:=J) z b (u,v))) {e} by
    simpa using Corona.list_cost (BB b) paid
  constructor
  · intro y hy
    refine halo_spec.mpr ⟨e,mem_singleton_self _,?_⟩
    rcases mem_insert.mp hy with rfl|other
    · simp
    · obtain ⟨v,_,rfl⟩:=mem_image.mp other
      rw [separation_comm]
      exact WilsonCapturedPrimaryReflectedGeometry.distance R z jb live home (u,v)
  · apply Corona.ship_halo
    intro x hx y hy
    obtain rfl:=mem_singleton.mp hx
    obtain rfl:=mem_singleton.mp hy
    exact .refl

theorem original (slow:WilsonWindowReportingPace.Slow R.kit) (J v:ℕ) (wide:4<v) (φ:Test n) :
    ∀ᶠ r:ℝ in 𝓝[>]0,
    let b:=WilsonCapturedPrimarySupportedHalo.date R r
    let k:=WilsonMeasuredWindow.stop (CF).path.levels simple v r
    J ≤ b ∧ b < k ∧ ∀N per (_live:k ≤ N) (z:Fin n → Site ((CF).side N per)),
    WilsonCenteredCompactBooking.mass R φ r (N,per) z ≠ 0 →
    ∀axis:Option (Fin n), let placedSites:=registered z axis
    (∀u:copy J per,∀a:Fin n,axis=some a →
      site R (J:=J) placedSites b (u,a)=(centerOf per J b) u) ∧
    (∀u:copy J per, ∀s:Finset (Fin n), coverNumber (BB b)
      (insert ((centerOf per J b) u) (s.image fun t=>site R (J:=J) placedSites b (u,t))) ≤ 1) ∧
    (∀u:copy J per, ∀i j:Fin n, coverNumber (BB b)
      ({site R (J:=J) placedSites b (u,i),site R placedSites b (u,j)}:Support _) ≤ 1) ∧
    (∀i, b ≤ i → i ≤ k → Cross (BB i) (site R (J:=J) placedSites i)) ∧
    Edition.Spaced (BB k) (site R (J:=J) placedSites k) ∧
    ∀a c:(copy J per)×Fin n, a ≠ c →
      (BB k)^2 < separation (site R (J:=J) placedSites k a) (site R placedSites k c) := by
  obtain ⟨M,diameter⟩:=φ.hasCompactSupport.exists_bound_of_continuousOn
    (continuous_id (X:=Points n)).continuousOn
  let K:=⌈M⌉₊
  have bound (x:Points n) (hx:x∈tsupport (fun x=>φ x)) (u:Fin n) (a:Axis) : |x u a| ≤ (K:ℝ) :=by
    have one:|x u a| ≤ ‖x u‖ :=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x u) a
    exact one.trans ((PiLp.norm_apply_le x u).trans ((diameter x hx).trans (Nat.le_ceil M)))
  have range:=(Multi.Wage.ranges simple (CF).path.levels).eventually_ge_atTop (2*(K+2)+2)
  obtain ⟨I₀,all⟩:=eventually_atTop.mp ((WilsonCapturedPrimaryReflectedGeometry.shell R J).and range)
  filter_upwards [Ioc_mem_nhdsGT ((CF).S.a_pos I₀),
    WilsonCapturedPrimarySeparatedStop.translated R simple slow v wide φ] with r small inside
  let b:=WilsonCapturedPrimarySupportedHalo.date R r
  let k:=WilsonMeasuredWindow.stop (CF).path.levels simple v r
  have rp:=small.1
  have valid:=small.2.trans ((CF).S.strictAnti.antitone (Nat.zero_le I₀))
  obtain ⟨fine,coarse⟩:=WilsonCloseCaptureDate.bracket (CF).S rp valid
  have late : I₀ ≤ b :=by
    by_contra! early
    have mono:=(CF).S.strictAnti.antitone (Nat.succ_le_of_lt early)
    exact (not_lt_of_ge mono) (fine.trans_le small.2)
  obtain ⟨⟨jb,margins⟩,large⟩:=all b late
  have earlier : b < k := (WilsonCloseCaptureDate.window R slow simple (by omega : 0<v) rp valid).1
  refine ⟨jb,earlier,?_⟩
  intro N per live z nonzero axis
  obtain ⟨x,hx,rfl⟩:=supported R φ r z nonzero
  let sites:=(seen r N per) x
  have liveB : b ≤ N :=earlier.le.trans live
  have raw (u:Fin n) : separation (((CF).S.toDepth liveB per).parent (sites u)) 0 ≤ K+2 :=by
    apply WilsonCapturedPrimaryCompactSites.ancestor (CF).S liveB (r • x) (K+1) _ u
    intro t a
    change |r*x t a|+(CF).S.a b ≤ ((K+1:ℕ):ℝ)*(CF).S.a b
    rw [abs_mul,abs_of_pos rp,Nat.cast_succ,add_mul,one_mul]
    exact add_le_add ((mul_le_mul coarse (bound x hx t a) (abs_nonneg _) ((CF).S.a_pos b).le).trans_eq
      (mul_comm _ _)) le_rfl
  let zeroSite:=axis.elim 0 sites
  let filed:=registered sites axis
  let g:=(CF).S.toDepth liveB per
  have originPaid : separation (g.parent zeroSite) 0 ≤ K+2 :=by
    cases axis with
    | none => simp [zeroSite,WilsonCapturedPrimarySubcellOrigin.origin]
    | some i => exact raw i
  have home (u:Fin n) : separation (g.parent (filed u)) 0 ≤ BB b :=by
    change separation (g.parent (sites u-zeroSite)) 0 ≤ _
    have shifted:=WilsonCapturedPrimarySubcellOrigin.distance (CF) liveB (sites u) zeroSite
    have cap:=raw u
    have triangle:=separation_triangle (g.parent (sites u)) 0 (g.parent zeroSite)
    rw [separation_comm 0 (g.parent zeroSite)] at triangle
    change separation (g.parent (sites u-zeroSite)) 0 < separation (g.parent (sites u)) (g.parent zeroSite)+2 at shifted
    change separation (g.parent (sites u)) 0 ≤ K+2 at cap
    change 2*(K+2)+2 ≤ BB b at large
    omega
  have anchorPaid (u:copy J per) (a:Fin n) (pinned:axis=some a) :
      site R (J:=J) filed b (u,a)=(centerOf per J b) u :=by
    apply WilsonReflectedMicroscopicSites.anchor R filed jb liveB a _ u
    have micro : filed a=0 :=by simp [filed,registered,pinned]
    rw [micro]
    simp only [WilsonThermometerOwnOffsetNectar.location,dif_pos liveB,
      WilsonThermometerOwnOffsetTale.site,WilsonCapturedPrimarySubcellOrigin.origin]
  have separate (i:ℕ) (left:b ≤ i) (right:i ≤ N) :=
    WilsonCapturedPrimaryReflectedGeometry.cross R simple filed jb liveB home (margins per jb) left right
  have pair:=inside N per live x hx zeroSite
  have collarPaid:=collar R filed (jb.trans earlier.le) live (J:=J)
  have allPairs : ∀a c:(copy J per)×Fin n, a ≠ c →
      (BB k)^2 < separation (site R (J:=J) filed k a) (site R filed k c) := by
    rintro ⟨u,a⟩ ⟨w,c⟩ ne
    by_cases same:u=w
    · subst w
      rw [collarPaid.widths u a c,WilsonReflectedMicroscopicSites.base R filed ((jb.trans earlier.le).trans live),
        WilsonReflectedMicroscopicSites.base R filed ((jb.trans earlier.le).trans live)]
      have keep:k ≤ N:=live
      simp only [WilsonThermometerOwnOffsetNectar.location,dif_pos keep,WilsonThermometerOwnOffsetTale.site]
      exact pair a c (fun eq=>ne (eq ▸ rfl))
    · exact separate k earlier.le live (u,a) (w,c) same
  exact ⟨anchorPaid,house R filed jb liveB home,WilsonCapturedPrimaryReflectedGeometry.oneBall R filed jb liveB home,
    (fun i bi ik a c sep=>(separate i bi (ik.trans live) a c sep).le),
    (fun a c ne=>(allPairs a c ne).le),allPairs⟩

end YM.Integration.WilsonCapturedPrimaryPhysicalArray

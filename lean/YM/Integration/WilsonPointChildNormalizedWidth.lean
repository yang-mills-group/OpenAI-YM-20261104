import YM.Integration.WilsonPointChildWidthPurchase
import YM.Integration.WilsonPointChildFiledSalary

/-! Common strong-width action of the original individually positioned
    step and the independently prescribed normalization at its own date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildNormalizedWidth
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonNeutralPointCourse WilsonPointChildFiledPress WilsonPointChildFiledSalary
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {d D:ℕ}

structure Wallet (o:Loc G 1)(F:Frame G d)(Y:Plaza F D)(b:ℝ)(e:ℕ)(C:ℝ):Prop where
  nonneg:0≤C
  tested:∀s:Letter F,∀p:Studio D,∀l≤e,∀r≤d+e,
    Knoxville (fame _) b (0,o) (Y s p l r) (C*‖p‖)

theorem Wallet.every {o:Loc G 1}{F:Frame G d}{Y:Plaza F D}{b C:ℝ}{e:ℕ}
    (h:Wallet o F Y b e C)(court:Court o F Y)(s:Letter F)(p:Studio D)(l:ℕ)(lh:l≤e)(r:ℕ):
    Knoxville (fame _) b (0,o) (Y s p l r) (C*‖p‖):=by
  by_cases hr:r≤d+e
  · exact h.tested s p l lh r hr
  · have z:Y s p l r=0:=by
      by_contra ne
      have hit:=(court.officers s).fare.1 p l r ne
      have cap:=slotsFits F s
      unfold Yield at hit
      omega
    rw [z];exact (Knox_zeros _).mono (mul_nonneg h.nonneg (norm_nonneg _))

theorem original (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (o:Loc G 1)(simple:G.Simple){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    (E r:ℕ):∀ᶠk:ℕ in atTop,∀(A B:Tour R k→ℕ→ℝ),
    (∀z j,k≤j→j≤z.cutoff→0≤A z j)→(∀z j,k≤j→j≤z.cutoff→1≤B z j)→
    (∀z j,k≤j→j<z.cutoff→Wallet o (R.family.labels.level d) (filed R wood a depth z.digit z.cutoff (j+1)) 0 E (A z (j+1)))→
    (∀z j,k≤j→j<z.cutoff→Wallet o (R.family.labels.level d) (filed R wood a depth z.digit z.cutoff (j+1)) (width R (j+1)) E (B z (j+1)))→
    ∃c:ℝ,∃v:ℕ,0≤c∧∀z:Tour R k,∀j,k≤j→j<z.cutoff→∀s:Letter (R.family.labels.level d),∀p:Studio D,
      Knoxville (fame _) (width R j) (0,o) (filed R wood a depth z.digit z.cutoff j s p E r)
        (inverseCost _ (transfer R wood a depth z.digit z.cutoff j)⁻¹ s E *
         (c*(max 1 (ageZ (R.family.path.levels.clock.hatBeta j)))^v*
          (((1+A z (j+1))*(B z (j+1))^(WilsonPinnedWidthTransport.fraction R.family.S (width R) j))*‖p‖))) :=by
  let days:=R.family.path.levels
  have cap:∀ᶠk:ℕ in atTop,d≤days.clock.J k:=days.fits.deep.eventually_ge_atTop _
  have lifted:=fun l:Fin (E+1)=>WilsonPointChildFiledPress.original R wood a depth o simple granted l.val r
  filter_upwards [cap, Filter.eventually_all.mpr lifted] with k rise intake
  intro A B ha hb lo hi
  have court (z:Tour R k)(j:ℕ)(kj:k≤j)(head:j<z.cutoff):=
    WilsonNeutralPointCourse.original R wood a depth z.digit z.cutoff (j+1) simple o head
      (rise.trans (days.fits.mono (by omega)))
  choose c v positive earn using fun l:Fin (E+1)=> intake l A B ha hb
    (fun z j kj head b p i il m=> (lo z j kj head).every (court z j kj head) b p i (il.trans (by omega)) m)
    (fun z j kj head b p i il m=> (hi z j kj head).every (court z j kj head) b p i (il.trans (by omega)) m)
  let M:=∑ l,c l
  let w:=∑ l,v l
  have cm (l:Fin (E+1)):c l≤M:=Finset.single_le_sum (fun i _=>positive i) (Finset.mem_univ l)
  have vw (l:Fin (E+1)):v l≤w:=Finset.single_le_sum (fun i _=>Nat.zero_le (v i)) (Finset.mem_univ l)
  refine ⟨M,w,Finset.sum_nonneg (fun l _=>positive l),?_⟩
  intro z j early live s p
  apply normalized R wood a depth o z.digit live
  intro b l hl
  let q:Fin (E+1):=⟨l,by omega⟩
  have receipt:=earn q z j early live b p
  apply receipt.mono
  have frac:(width R j/(R.family.S.block j).val)/width R (j+1) =
      WilsonPinnedWidthTransport.fraction R.family.S (width R) j:=by
    unfold WilsonPinnedWidthTransport.fraction
    ring
  rw [frac]
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul (cm q) (pow_le_pow_right₀ (le_max_left 1 _) (vw q))
      (pow_nonneg (zero_le_one.trans (le_max_left 1 _)) _) (Finset.sum_nonneg (fun i _=>positive i))
  · exact mul_nonneg (mul_nonneg (add_nonneg zero_le_one (ha z (j+1) (by omega) live))
      (Real.rpow_nonneg (zero_le_one.trans (hb z (j+1) (by omega) live)) _)) (norm_nonneg _)

end YM.Integration.WilsonPointChildNormalizedWidth

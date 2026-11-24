import YM.Integration.WilsonPointChildTerminalWidth
import YM.Integration.WilsonPointChildWidthPortfolio

/-! Finiteness at the actual original price of every intermediate rooted
    tensor is established before using the all-cutoff quantitative bound. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildWidthEntrance
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Dove.Lab Sierra
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNormalizedWidth WilsonPointChildFreight WilsonPointChildPressIncome WilsonPointChildPressCalendar
open WilsonNeutralPointCourse WilsonPointChildFiledPress WilsonPointChildFiledSalary WilsonPointChildWidthPortfolio
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d D:ℕ}
variable (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)(o:Loc G 1)
variable {E k:ℕ}(registered:∀(X:Type)(C:Pin (estate X R wood k).scrolls)(a:hue G),
  WilsonPointChildPressCalendar.bill (estate X R wood k) C R.metals.O a E)

include registered in
private theorem single {N j:ℕ}(kj:k≤j)(live:j<N)(Y:Plaza (R.family.labels.level d) D)
    (court:Court o (R.family.labels.level d) Y)(H:ℝ)(cost:Wallet o _ Y (width R (j+1)) E H)
    (digit:∀i,Site (R.family.S.block i))(l:ℕ)(le:l≤E)(m:ℕ):
    ∃C:ℝ,0≤C∧∀b:Letter (R.family.labels.level d),∀p:Studio D,Knoxville (fame _) (width R j) (0,o)
      (forward R wood a digit N j Y b p l m) (C*‖p‖):=by
  let X:=Letter (R.family.labels.level d)
  let W:=estate X R wood k
  let C:Pin W.scrolls:=⟨fun _=>N,fun _=>kj.trans live.le⟩
  let T:Turn C→Anthem D G:=fun z=>if z.b=j then Y z.a else 0
  let B:=max 1 H
  have bp:1≤B:=le_max_left ..
  have bn:0≤B:=zero_le_one.trans bp
  let roof (z:Turn C):=B
  have all (i:ℕ)(ih:i≤l)(r:ℕ)(z:Turn C)(p:Studio D):
      Knoxville (fame _) (W.stub z) (0,o) (T z p i r) (roof z*‖p‖):=by
    by_cases hit:z.b=j
    · rw [show T z=Y z.a by simp [T,hit]]
      have same:W.stub z=width R (j+1):=congrArg (fun h=>width R (h+1)) hit
      rw [same]
      exact ((cost.every court _ _ _ (ih.trans le) _).mono (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)))
    · rw [show T z=0 by simp [T,hit]]
      exact (Knox_zeros _).mono (mul_nonneg bn (norm_nonneg _))
  obtain ⟨c,v,cn,buy⟩:=registered X C a D d d l m le o T roof roof (fun _=>bn) (fun _=>bp)
    (fun i ih r z p=> penn_shrink (all i ih r z p) ((Primer.FamilyWindow R.family).pos _).le) all
  let day:=max 1 (ageZ (R.family.path.levels.clock.hatBeta j))
  let θ:=(width R j/(R.family.S.block j).val)/width R (j+1)
  let M:=c*day^v*((1+B)*B^θ)
  refine ⟨M,mul_nonneg (mul_nonneg cn (pow_nonneg (zero_le_one.trans (le_max_left ..)) _))
    (mul_nonneg (add_nonneg zero_le_one bn) (Real.rpow_nonneg bn _)),?_⟩
  intro b p
  let z:Turn C:=⟨⟨b,j,kj⟩,live⟩
  have h:=buy z p (digit j)
  rw [scaled,show T z=Y b by simp [T,z]] at h
  change Knoxville (fame _) (width R j) (0,o) (forward R wood a digit N j Y b p l m)
    (c*day^v*((1+B)*B^θ*‖p‖)) at h
  simpa only [M,mul_assoc] using h

include registered in
private theorem local_step {N j:ℕ}(kj:k≤j)(live:j<N)(digit:∀i,Site (R.family.S.block i))
    (court:Court o (R.family.labels.level d) (filed R wood a depth digit N (j+1)))
    (H:ℝ)(cost:Wallet o _ (filed R wood a depth digit N (j+1)) (width R (j+1)) E H):
    ∃B:ℝ, Wallet o (R.family.labels.level d) (filed R wood a depth digit N j) (width R j) E B:=by
  let Y:=filed R wood a depth digit N (j+1)
  let X:=Fin (E+1)×Fin (d+E+1)
  choose Q paid bounds using fun i:X=>single R wood a o registered kj live Y court H cost digit i.1.val (by omega) i.2.val
  let M:=∑x,Q x
  have mn:0≤M:=Finset.sum_nonneg fun _ _=>paid _
  have mq (x:X):Q x≤M:=Finset.single_le_sum (fun i _=>paid i) (Finset.mem_univ x)
  let S:=(transfer R wood a depth digit N j)⁻¹
  refine ⟨invoice _ S E*M,⟨mul_nonneg (zero_le_one.trans (invoice_pos ..)) mn,?_⟩⟩
  intro s p l ll r rr
  have q:=normalized R wood a depth o digit live (width R j) (M*‖p‖) s p l r
    (fun b i ih=>(bounds (⟨i,by omega⟩,⟨r,by omega⟩) b p).mono
      (mul_le_mul_of_nonneg_right (mq _) (norm_nonneg _)))
  apply q.mono
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (invoice_pays _ S ll s) mn) (norm_nonneg _)

theorem original (simple:G.Simple){orders:ℕ→ℕ}
    (granted:WilsonWindowFormalPurchase.Canonical orders R.kit)(E:ℕ):
    ∀ᶠk:ℕ in atTop,∀z:Tour R k,∀j,k≤j→j≤z.cutoff→
      ∃B:ℝ, Wallet o (R.family.labels.level d) (filed R wood a depth z.digit z.cutoff j) (width R j) E B:=by
  obtain ⟨c,w,_,bare⟩:=WilsonPointChildTerminalWidth.original R wood a depth o simple granted E
  obtain ⟨k₀,top⟩:=eventually_atTop.mp bare
  filter_upwards [eventually_ge_atTop k₀, R.family.path.levels.fits.deep.eventually_ge_atTop d,
    WilsonPointChildPressCalendar.original R wood simple granted E] with k late enough registered
  intro z j kj live
  induction live using Nat.decreasingInduction with
  | self =>exact ⟨_,top _ (late.trans z.live) z.digit⟩
  | of_succ j head ih =>
    obtain ⟨H,h⟩:=ih (by omega)
    have court:=WilsonNeutralPointCourse.original R wood a depth z.digit z.cutoff (j+1) simple o head
      (enough.trans (R.family.path.levels.fits.mono (by omega)))
    exact local_step R wood a depth o registered kj head z.digit court H h

end YM.Integration.WilsonPointChildWidthEntrance

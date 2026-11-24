import YM.Integration.WilsonPointChildCoverReturn
import YM.Integration.WilsonPointChildFiledTest
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildCoveredRead
open Filter Function Finset YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial Rift Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep WilsonPointChildFiledPress
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical ENNReal
variable {G:Gauge}{d D:ℕ}

theorem directions {V:Type}{r:ℕ}{D:Reach V}{b B:ℝ}{z:V}{T:Tile V r}
    (h:Knoxville D b z T B)(bb:0≤b)(A:V→ℝ)(a:ℝ≥0∞)(cap:∀x,‖A x‖ₑ≤a):
    (∑' x:chain V r,‖T x‖ₑ*∏t,‖A (x t)‖ₑ)≤ENNReal.ofReal B*a^r:=by
  have amp(x:chain V r):(∏t,‖A (x t)‖ₑ)≤a^r:=by
    simpa using (Finset.prod_le_prod' (s:=Finset.univ) (g:=fun _:Fin r=>a) (fun t _=>cap (x t)))
  have root(x:chain V r):‖T x‖ₑ ≤ shine b (wide D (Fin.cons z x))*‖T x‖ₑ:=by
    have one:(1:ℝ≥0∞) ≤ shine b (wide D (Fin.cons z x)):=by
      simpa [Gorge.shine] using (Gorge.shine_le b bb (Nat.zero_le (wide D (Fin.cons z x))))
    simpa only [one_mul] using (mul_le_mul_left one ‖T x‖ₑ)
  calc
    _ ≤ ∑' x:chain V r,(shine b (wide D (Fin.cons z x))*‖T x‖ₑ)*a^r:=
      ENNReal.tsum_le_tsum (fun x=>mul_le_mul' (root x) (amp x))
    _ ≤ _:=by rw [ENNReal.tsum_mul_right];exact mul_le_mul_left h.2 _

theorem original (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (u:G.ColorIndex)(depth:d<D)(o:Loc G 1)(E:ℕ){η:ℝ}(positive:0<η):
    ∀ᶠi:ℕ in atTop,∀N,i≤N→∀v:Letter (R.family.labels.level d),∀e≤E,∀r:ℕ,
    let F:=WilsonPointChildCoverReturn.table R u depth N (N-i) i v
    let B:=((R.family.path.levels.clock.hatBeta i)^η)
    (∀p:Scroll D,Knoxville (fame _) (width R i) (0,o) (F p e r) (B*‖physical p‖)) ∧
    ∃K:chain (edgeL G) r→Pen (fun _:Unit=>D) {()},
      (∀x (p:Scroll D),touch (fun _:Unit=>page D p) {()} (K x)=F p e r x) ∧
      Wig terrain (fun _:Unit=>0) (width R i) (WilsonPointChildTestJet.rent D*B) {()} K:=by
  let V:=R.family.path.levels
  have reach:=V.fits.deep.eventually (eventually_ge_atTop d)
  filter_upwards [booked (routes R) u depth o E positive,reach] with i eligible awake
  intro N live v e ee r F B
  obtain ⟨w,reading⟩:=eligible N live
  have io:∀j:ℕ,i≤j → j<N → d≤V.clock.J (j+1):=fun j ij _=>awake.trans (V.fits.mono (by omega))
  have calcF(p:Scroll D):F p=WilsonNeutralPointCourse.filed R (routes R) u depth (fun _=>0) N i v (physical p):=
    WilsonPointChildCoverReturn.original R u depth simple o _ _ _ (by omega) io _ _
  have court:=WilsonNeutralPointCourse.original R (routes R) u depth (fun _=>0) N i simple o live
    (awake.trans (V.fits.mono (Nat.le_succ _)))
  obtain ⟨K,read,rate⟩:=reading v e ee r
  refine ⟨fun p=>?_,K,fun x p=>?_,rate⟩
  · rw [calcF];exact (w _).every court v (physical p) e ee r
  · rw [calcF];exact read x p

end YM.Integration.WilsonPointChildCoveredRead

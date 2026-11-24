import YM.Integration.WilsonNeutralPointWeakSchool
import YM.Integration.WilsonNeutralPointWeakYears
import YM.Integration.WilsonNeutralPointCourse

/-! A weak before-cutoff price for each original normalized field and matrix
coefficient, on a common Wilson trajectory and every separately chosen child. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointWeakDated
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove Dove.Lab
open Quire Palm Grail Chapel Borough Sable Tundra Aster Clover Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonNeutralPointWeakSchool WilsonNeutralPointWeakYears
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d D E w:ℕ}(R:Run G)(wood:Primer.Families R.family)(depth:d<D){U:ℕ→ℕ}

abbrev field {X:Type}{k:ℕ}(C:Pin (campus R X wood k).scrolls)(a:hue G)
    (digits:X→∀j,Site (R.family.S.block j))(x:Deck C):Plaza (R.family.labels.level d) D:=
  WilsonNeutralPointCourse.filed R wood a depth (digits x.a) (C.N x.a) x.b

abbrev matrix {X:Type}{k:ℕ}(C:Pin (campus R X wood k).scrolls)(a:hue G)
    (digits:X→∀j,Site (R.family.S.block j))(x:Turn C):Tilework (R.family.labels.level d):=
  WilsonNeutralPointCourse.transfer R wood a depth (digits x.a) (C.N x.a) x.b

theorem original (simple:G.Simple)(granted:WilsonWindowFormalPurchase.Canonical U R.kit)
    (strong:WilsonNeutralPointForecast.Filed R.kit)(weak:WilsonNeutralPointWeakForecast.Filed R.kit):
    ∀ᶠk:ℕ in atTop,∀(X:Type)(C:Pin (campus R X wood k).scrolls)(a:hue G)(o:Loc G 1)
      (digits:X→∀j,Site (R.family.S.block j)),
    (∀v e,e≤E→∀r,Row C o (R.family.labels.level d) (max w ((d+1)*(d+1)))
      (field R wood depth C a digits) v e r) ∧
    ∀v y j,j≤E→Soft (tide C) (fun i=>coeff j (matrix R wood depth C a digits i y v)):=by
  let A:=R.family.path.levels
  have grows:Tendsto (fun k:ℕ=>A.clock.J (k+1)) atTop atTop:=A.fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [WilsonNeutralPointWeakSchool.original (E:=E) (w:=w) R depth wood strong weak,
    grows.eventually_ge_atTop (max d (E+5))] with k salary fit X C a o digits
  let Z:=campus R X wood k
  let F:=R.family.labels.level d
  have opening:Evergreens (Primer.Noise R.family) Spigot.herald R.family.labels.level R.family.params
      (chart G) (Primer.FamilyWindow R.family) A:=(WilsonWindowFormalAnnouncement.on_run R granted).power
  have poster:Poster (Primer.Noise R.family) Spigot.herald R.family.labels.level R.family.params (chart G) Z (E+5):=
    presold simple (W:=Primer.FamilyWindow R.family) (U:=Z.toEmpire) (fun _=>opening) Z.neck (by omega) (fun _=>(le_max_right ..).trans fit)
  have eligible:Z.Use R.metals.O E:=by rw [granted.1];exact poster.vac E (by omega)
  have wells:=Elm.grasp eligible C C (fun _=>le_rfl) R.alloy.B.ratio simple a
  have credit:Soft (tide C) (fun i=>(Z.sail i)⁻¹):=by
    refine ⟨1,1,zero_le_one,fun i=>?_⟩
    obtain ⟨c,_,cost,bills⟩:=opening.payment i.b
    have receipt:=bills.header (A.clock.J i.b) (A.fits.mono (Nat.le_succ i.b))
    simp only [one_mul,pow_one]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (receipt.trans (cost.trans (le_max_right ..)))
  have floor (i:Deck C):d≤A.clock.J (i.b+1):=
    ((le_max_left d (E+5)).trans fit).trans (A.fits.mono (Nat.add_le_add_right i.zone 1))
  have current (i:Deck C):Court o F (field R wood depth C a digits i):=
    WilsonNeutralPointCourse.original R wood a depth (digits i.a) (C.N i.a) i.b simple o i.cap (floor i)
  have issued (i:Turn C):=WilsonNeutralPointCourse.received R wood a depth (digits i.a)
    (C.N i.a) i.b simple o i.head (floor i.bed)
  apply WilsonNeutralPointWeakYears.original C eligible.liable F _ _ current
  · intro v e r he hr old lower
    exact WilsonNeutralPointWeakTransfer.column wells credit (fun i=>Elm.growL (Z.V i.a) i.b)
      (fun i=>digits i.a i.b) (salary X C o (fun i=>digits i.a i.b)) v he hr
      (fun i=>current i.ups) (fun i=>current i.bed) (matrix R wood depth C a digits)
      (fun _=>rfl) (fun i=>(issued i).1) (fun i=>(issued i).2) old lower
  · intro v e he r
    have base (x:X):field R wood depth C a digits (peak C x)=sectionY (R.family.localSection d) depth:=
      WilsonNeutralPointCourse.top R wood a depth (digits x) (C.N x)
    simp_rw [base]
    exact WilsonNeutralPointWeakYears.bare F _ depth v he o _ r _

end YM.Integration.WilsonNeutralPointWeakDated
end

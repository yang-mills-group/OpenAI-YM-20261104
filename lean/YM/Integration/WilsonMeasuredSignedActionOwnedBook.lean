import YM.Integration.WilsonMeasuredSignedActionOwnedRows
import YM.Integration.WilsonMeasuredSignedActionReserve
/-! The same bounded physical book at the named original reporting table,
with exact equality of the unamplified weak coordinate. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionOwnedBook
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}{lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family

open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourWeakWall (Purchased)
open WilsonPositionProgramPublicStations (Pair)
open WilsonThermometerUnitFilingFourSquare (Arm)


open WilsonMeasuredSignedActionOwnedRows (Rows)
open WilsonMeasuredPublicEntranceNativeFrame (atRadius)
open PhysMS

def sub {δ e:ℝ}(incl:e≤δ)(r:{s:ℝ // 0<s ∧ s<e}):Set.Ioc (0:ℝ) δ:=
  ⟨r.val,r.property.1,r.property.2.le.trans incl⟩

theorem mounted {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(W:∀s,Vane C (cap s))
    (prior:ℝ→tower S)(s:Set.Ioc (0:ℝ) δ){D T:ℕ}
    (stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T s.val)
      (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T s.val)^T))
    (real:(W s).wheel.r=s.val)(honest:(W s).checked order H (cap s))
    (sold:Rows (f:=order) (S:=S) (l:=l) (W s) s.val D):
    ∃B:Book F (l:=l) H z D T s.val,B.k=cap s ∧ B.W.k=(W s).k ∧ HEq B.W (W s) ∧
      ∀e:Fin (D+1),B.V e=atRadius l cap W prior s.val e:=by
  have row (e:Fin (D+1)):∃U:Spin.change S e.val,U=atRadius l cap W prior s.val e ∧
      Nonempty (Pair F stock (Nat.le_of_lt_succ e.isLt) (W s) sold.fits U s.val):=by
    obtain ⟨U,priced,filed⟩:=sold.filed e
    have same:=WilsonMeasuredPublicEntranceNativeFrame.at_site l cap W prior s
      ((Nat.le_of_lt_succ e.isLt).trans sold.fits) priced
    choose arm kept salary using filed
    let weak(y:S.Field e.val):Arm R.family S (l:Filter _) e.val y:=
      let a:=arm (U.symm y)
      ⟨a.source,a.label,a.approaches,a.represents.trans (U.apply_symm_apply y)⟩
    let both(b:Bool)(y:S.Field e.val):Arm R.family S (l:Filter _) e.val y:=
      if b then weak y else ((stock.department e.val (Nat.le_of_lt_succ e.isLt)).print y).arm
    refine ⟨U,same.symm,⟨⟨both,fun _=>rfl,fun y p=>kept (U.symm y) p,fun y=>?_⟩⟩⟩
    exact salary (U.symm y)
  choose U named sale using row
  exact ⟨⟨stock,cap s,W s,sold.fits,honest,real,U,fun e=>Classical.choice (sale e)⟩,
    rfl,rfl,HEq.rfl,named⟩

theorem cofinal {δ:ℝ}{cap:Set.Ioc (0:ℝ) δ→ℕ}(W:∀s,Vane C (cap s))
    (calendar:∀s:ℕ→Set.Ioc (0:ℝ) δ,Tendsto (fun n=>(s n).val) atTop (𝓝 0)→
      Tendsto (fun n=>cap (s n)) atTop atTop ∧ Tendsto (fun n=>(W (s n)).k) atTop atTop)(j:ℕ):
    ∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r→j≤cap s ∧ j≤(W s).k:=by
  by_contra no
  obtain ⟨rr,shrink,bad⟩:=contradictionTrail _ no
  have fail(n:ℕ):∃s:Set.Ioc (0:ℝ) δ,s.val=rr n ∧ ¬(j≤cap s ∧ j≤(W s).k):=by
    by_contra raw
    apply (bad n).2
    intro s loc
    by_contra missing
    exact raw ⟨s,loc,missing⟩
  choose s atR misses using fail
  have small:Tendsto (fun n=>(s n).val) atTop (𝓝 0):=by simpa only [atR] using shrink.mono_right nhdsWithin_le_nhds
  obtain ⟨a,b⟩:=calendar s small
  obtain ⟨n,can⟩:=((a.eventually_ge_atTop j).and (b.eventually_ge_atTop j)).exists
  exact misses n can

theorem original (simple:G.Simple)(bliss:Bliss F l z H){δ:ℝ}(positive:0<δ)
    (cap:Set.Ioc (0:ℝ) δ→ℕ)(W:∀s,Vane C (cap s))(prior:ℝ→tower S)
    (real:∀s,(W s).wheel.r=s.val)(honest:∀s,(W s).checked order H (cap s))
    (calendar:∀s:ℕ→Set.Ioc (0:ℝ) δ,Tendsto (fun n=>(s n).val) atTop (𝓝 0)→
      Tendsto (fun n=>cap (s n)) atTop atTop ∧ Tendsto (fun n=>(W (s n)).k) atTop atTop)(D:ℕ):
    ∃T:ℕ,∃e:ℝ,0<e ∧ ∃incl:e≤δ,∃B:(s:{s:ℝ // 0<s ∧ s<e})→Book F (l:=l) H z D T s.val,
      (∀s,(B s).k=cap (sub incl s) ∧ (B s).W.k=(W (sub incl s)).k ∧ HEq (B s).W (W (sub incl s)) ∧
              ∀i:Fin (D+1),(B s).V i=atRadius l cap W prior s.val i) ∧
      ∀j:ℕ,∀ᶠr in trail,∀p:0<r,∀small:r<e,j≤(B ⟨r,p,small⟩).k ∧ j≤(B ⟨r,p,small⟩).W.k:=by
  obtain ⟨T,stocks⟩:=WilsonPositionProgramPublicStations.original F simple bliss D
  have earns:=WilsonMeasuredSignedActionOwnedRows.original F simple cap W R.makes bliss real honest calendar D
  obtain ⟨η,pos,held⟩:=Metric.mem_nhdsWithin_iff.mp (stocks.and earns)
  let e:=min η δ
  have valid:0<e:=lt_min pos positive
  have incl:e≤δ:=min_le_right ..
  have sale(s:{s:ℝ // 0<s ∧ s<e}):∃B:Book F (l:=l) H z D T s.val,
      B.k=cap (sub incl s) ∧ B.W.k=(W (sub incl s)).k ∧ HEq B.W (W (sub incl s)) ∧
        ∀i:Fin (D+1),B.V i=atRadius l cap W prior s.val i:=by
    have cash:=held (show s.val∈Metric.ball 0 η ∩ Ioi (0:ℝ) from
      ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos s.property.1] using
        s.property.2.trans_le (min_le_left η δ),s.property.1⟩)
    obtain ⟨stock,_⟩:=cash.1.1
    exact mounted F cap W prior (sub incl s) stock (real _) (honest _) (cash.2 _ rfl)
  choose B named using sale
  refine ⟨T,e,valid,incl,B,named,fun j=>?_⟩
  filter_upwards [cofinal W calendar j] with r late
  intro hp small
  let s:{s:ℝ // 0<s ∧ s<e}:=⟨r,hp,small⟩
  have current:=late (sub incl s) rfl
  exact ⟨(named s).1.symm ▸ current.1,(named s).2.1.symm ▸ current.2⟩

end YM.Integration.WilsonMeasuredSignedActionOwnedBook
end

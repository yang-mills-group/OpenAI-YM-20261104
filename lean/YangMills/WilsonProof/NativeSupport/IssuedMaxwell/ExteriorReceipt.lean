import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.ExteriorReceipt
open YM YM.Integration YM.FVA2
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project O.Read O.Canon
variable (g:YangMills.GaugeGroup)(simple:g.IsSimple){n:ℕ}

include simple in
theorem original (u:Scan g.core n):
    let V:=wave (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)
    let p:=LogPricing V u
    OPEA (install V) u p ∧ (∀q:FLog g.core n,OPEA (install V) u q→q=p) ∧
    ∀(K:Set (Points n)),IsCompact K→K⊆conf n→∀(h k m:ℕ)(E:Set (Points m))(v:Scan g.core m),
      IsCompact E→E⊆Outside m→∃C:ℝ,0<C ∧ ∃L:ℕ,∀ᶠ t:ℝ in atTop,∀x∈K,∀y∈E,
        ‖coeff k (Submit (install V) u v t p h x y)‖≤
          C*(1+t)^L*Real.exp (((totalG u:ℝ)-(h:ℝ)-1)*t):=by
  obtain ⟨σ,matched⟩:=(ElectedPrescription.original g simple).2.2.2.2 false
  have physical:=(matched.separatedOPE (Teller.logNu 1)).continuum
  have paid:=physical.works u
  refine ⟨paid,fun q hq=>(physical.unique u hq).symm,?_⟩
  intro K ck sep h k m E v ce ext
  obtain ⟨C,hC,L,rain⟩:=(paid.through K ck sep h (k+1) m E v ce ext) k (Nat.lt_succ_self k)
  refine ⟨C,hC,L,?_⟩
  filter_upwards [rain] with t bound
  intro x hx y hy
  have row:=bound (⟨x,hx⟩,⟨y,hy⟩)
  simpa only [post,neg_sub,sub_sub,neg_add_rev,neg_neg,mul_assoc] using row
end IssuedMaxwell.ExteriorReceipt
end

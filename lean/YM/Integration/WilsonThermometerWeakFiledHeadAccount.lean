import YM.Integration.WilsonThermometerWeakHeadRent
import YM.Integration.WilsonThermometerWeakGroupSpirit
import YM.Integration.WilsonThermometerWeakGroupTariff
import YM.Integration.WilsonThermometerWeakColumnRead

/-! File the weak group observable on the very coefficient returned by the joint
reflected Wilson push. The same polynomial pays its original healthy aperture
and its self-contracted primary in the true covariance units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFiledHeadAccount
open Function Filter Set MeasureTheory RG RG12 Extra.Histories Lattice Wilson
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Source Labels Next.Rank.Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels
local notation "Corr" => WilsonThermometerWeakWickRoom.corrected R

theorem original (simple:G.Simple) (d D:ℕ) (hd:d≤D) (S:Rules G) :
    ∀ᶠ k:ℕ in atTop,∀ N (_:k≤N) p,
    let P:=(C).path.rep N p k
    let b:=sizeQ C k
    let m:=scouts C k
    let F:=(C).labels.level d
    let s:=clim (Lev) k
    let g:=GaugeScale C k N p
    ∃ (K:Provision C d k N p m b) (wide:4*b≤wood (Lev) k),D+1≤P.p.order →
    ∀ (X:Coefficient F ((C).side k p)) {cash:ℝ},X.Format 0 (C).params P →
      X.remBound 0 P (kappa (C).path k) cash →
    let cap:=2*((Lev).params k).columns*F.coeffSize X.x
    ∃ q:poly (Up C k p b),
      coin (sender K.length P.p.threshold g q)≤(cap+2*cash)*bill (1/2) s ∧
      q.totalDegree≤D ∧ Spirit (sender K.length P.p.threshold g q) ∧
      (∀ U:Config G ((C).side k p),Healthy (tau (Lev) k) (Spindle.patch b 0) U →
       ‖X.exponentialEntry 0 ((C).localSection d) P U-signet 0 g (sender K.length P.p.threshold g q) U‖≤
        (cap+cash)*bill (-(D:ℝ)) s) ∧
      (∀ E:AtlasData G (C).S p,Hail C k p D E →
        coin (Corr K.length wide (control (k:=k) E 0 (wood (Lev) k)) q N d-expose F X.x)
          ≤(cap+cash)*bill (-(1/2)) s) := by
  filter_upwards [WilsonThermometerWeakHeadRent.original R simple S D,WilsonThermometerWeakPrimaryRead.funded R simple S d D hd,
      WilsonThermometerWeakWickRoom.funded R simple S d D hd,
      WilsonThermometerWeakGroupTariff.original C simple R.makes S D] with k billed main reg physical N hk p P b m F s g
  obtain ⟨K,wide,prim⟩:=main N hk p
  obtain ⟨_,_,remain⟩:=reg N hk p
  refine ⟨K,wide,?_⟩
  intro degree X cash format paid cap
  obtain ⟨a,q,na,ca,report,coarse⟩:=prim X.x degree
  obtain ⟨e,u,v,ne,ce,near,far,noise⟩:=remain X format paid degree
  have capEq:2*(((Lev).params k).columns*F.coeffSize X.x)=cap:=by dsimp [cap];ring
  refine ⟨q+(u+v),?_,?_,?_,?_,?_⟩
  · rw [←capEq];exact billed N hk p X K wide na ca ne ce report near far
  · have hq:=report.choose_spec.2.produced.choose_spec.1.degree
    have hu:=near.choose_spec.2.produced.choose_spec.1.degree
    have hv:=far.choose_spec.2.produced.choose_spec.1.degree
    exact totalDegree_add .. |>.trans (max_le hq ((totalDegree_add ..).trans (max_le hu hv)))
  · apply WilsonThermometerWeakGroupSpirit.field;intro x t
    have h₁:=WilsonThermometerWeakGroupSpirit.represented report x t
    have h₂:=WilsonThermometerWeakGroupSpirit.represented near x t
    have h₃:=WilsonThermometerWeakGroupSpirit.represented far x t
    simpa only [map_add] using congrArg₂ (·+·) h₁ (congrArg₂ (·+·) h₂ h₃)
  · intro U healthy
    rw [←capEq];exact physical N hk p K X format na ca ne ce report near far U healthy
  · intro E hail
    let Q:=control (k:=k) E 0 (wood (Lev) k)
    let Z:=Corr K.length wide Q q N d
    let H:=Corr K.length wide Q (u+v) N d
    let x:=expose F X.x
    have eq : Corr K.length wide Q (q+(u+v)) N d-x=(Z-x)+H := by rw [WilsonThermometerWeakColumnRead.add];dsimp [Z,H];abel
    change coin (Corr K.length wide Q (q+(u+v)) N d-x)≤_
    rw [eq,←capEq]
    refine (taller 0 zero_le_one _ _).trans ((add_le_add (coarse E hail) (noise Q hail.2)).trans_eq ?_)
    ring

end YM.Integration.WilsonThermometerWeakFiledHeadAccount
end

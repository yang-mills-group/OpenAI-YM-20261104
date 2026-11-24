import YM.Integration.WilsonThermometerWeakFlagStrike
import YM.Integration.WilsonThermometerWeakLongReading

/-! All coefficients in one displaced physical singleton are reissued on the measured
weak-course shelves. The genuinely long rows keep their own original supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakOriginalShelves
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Configuration Rise Normal Source.Drops
open Thirst Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential
open Beamer Common LiftMark Glimmer Station Asymptotics MvPolynomial Ribbon
open WilsonThermometerWeakTaylor WilsonThermometerWeakRetainedRow
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels

theorem purchased (simple:G.Simple) (d D:ℕ) (hd:d≤D) (S:Rules G) :
    ∀ᶠ k:ℕ in atTop,∀ N (_:k≤N) p,
    let P:=(C).path.rep N p k
    let b:=sizeQ C k;let m:=scouts C k;let n:=(C).side k p
    let Z:=Spindle.patch b (0:Site n); let F:=(C).labels.level d
    let g:=GaugeScale C k N p;let v:=bill (-(D:ℝ)) (clim (Lev) k)
    ∀ (K:Provision C d k N p m b) (X:Coefficient F n) (L:poly (Up C k p b)),
      ∀ {cash δ:ℝ},D+1≤P.p.order → X.Format 0 (C).params P →
      X.remBound 0 P (kappa (C).path k) cash → 0≤δ →
      let W:=sender K.length P.p.threshold g L;let T:=signet 0 g W
      let cap:=2*((Lev).params k).columns*F.coeffSize X.x
      Spirit W → (∀ U,Healthy (tau (Lev) k) Z U→‖X.exponentialEntry 0 ((C).localSection d) P U-T U‖≤δ) →
      ∀ (q:BudgetPoint) (_:q.threshold=tau (Lev) k) (_:Lower P.p q)
        (V:Type) [Fintype V] [DecidableEq V] (ζ:V→Site n) (s:Signed) (r:Prop) (x:V),
      ∃ (file error:SourceAt G ζ) (forced:Strike G ζ q.threshold) (far:Keepat n → SourceAt G ζ),
       file.extent=swath s (ζ x) Z ∧ file.fires=slot x ∧ file.value=dot r ∘ T ∘ pull s (ζ x) ∧
       error.extent=swath s (ζ x) Z ∧ error.fires=slot x ∧ forced.extent=halo 8 (swath s (ζ x) Z) ∧
       forced.fires=slot x ∧ (∀ j,(far j).extent=swath s (ζ x) j.val ∧ (far j).fires=slot x) ∧
       (∀ U,Poly.send (slot x) (dot r (X.exponentialEntry 0 ((C).localSection d) P (pull s (ζ x) U)))=
        file.amount q.threshold U+error.amount q.threshold U+forced.occ U+∑ j,(far j).amount P.p.threshold U) ∧
       ∀ (w:V→ℝ),0≤w x →
         transported error q.threshold w (w x*(δ+v*cash)) ∧ Taxed forced (q:=q) w (w x*(cap+‖X.x 0‖+cash)) ∧
        ∀ y:ℝ,0≤y→scalesExp P.p q (2*y)→∃ c:Keepat n→ℝ,
          (∀ j,transported (far j) P.p.threshold w (c j)) ∧
          (∑ j,c j*debt q.B y (halo 8 (far j).extent))≤Real.exp (100000*y)*Real.exp (-(P.p.supportExponent*m)/2)*(w x*cash) := by
  filter_upwards [WilsonThermometerWeakPrimaryRead.funded R simple S d D hd,
      WilsonThermometerWeakWickRoom.funded R simple S d D hd,shrank C (D:ℝ) simple R.makes] with k main reg thin N hk p P b m n Z F g v K X L cash δ degree form rem δ0 W T cap spirit fit q threshold low V _ _ ζ s r x
  obtain ⟨_,_,prim⟩:=main N hk p
  obtain ⟨_,_,occ⟩:=reg N hk p
  obtain ⟨a,a0,_,_,aa,_⟩:=prim X.x degree
  obtain ⟨e,u,l,_,_,near,far,_⟩:=occ X form rem degree
  have capEq:2*(((Lev).params k).columns*F.coeffSize X.x)=cap:=by dsimp [cap];ring
  rw [capEq] at aa
  obtain ⟨rh,rr,same,gross,distantFee,whole⟩:=WilsonThermometerWeakRetainedRow.original K X form aa near far
  have fresh:Reliable q.threshold G n Z T:=by
    have a:=origin0 W spirit g (0:Site n);exact ⟨a.inv,a.meas,a.locally⟩
  have nonnegCash:0≤cash:=(norm_nonneg _).trans ((WilsonThermometerWeakGroupAperture.deposit near (1:Config G n)).2)
  have v0:0≤v:=(Real.exp_pos _).le
  have score U (h:Healthy q.threshold Z U):‖short X N m U-T U‖≤δ+v*cash:=by
    have eq:short X N m U-T U=(X.exponentialEntry 0 ((C).localSection d) P U-T U)-distant X N m U:=by rw [whole U];abel
    rw [eq];apply (norm_sub_le ..).trans;apply add_le_add (fit U (threshold ▸ h))
    exact (distantFee U).trans (mul_le_mul_of_nonneg_right (thin N hk p) nonnegCash)
  let Y:Keepat n:=⟨Z,by rw [doors,separation_self];exact Nat.zero_le _⟩
  obtain ⟨A,E,H,fA,eX,eS,hX,hS,read,pay⟩:=
    WilsonThermometerWeakFlagStrike.original X Y T rh rr same fresh gross score (add_nonneg δ0 (mul_nonneg v0 nonnegCash)) low.good ζ s r x
  let B:=WilsonThermometerWeakLongOccurrences.filed X form m (ζ:=ζ) s r x
  refine ⟨A,E,H,B,?_,?_,?_,eX,eS,hX,hS,fun _=>⟨rfl,rfl⟩,?_,?_⟩
  · rw [fA];rfl
  · rw [fA];rfl
  · rw [fA];rfl
  · intro U;rw [whole _,dot_add,send_plus,read U]
    rw [WilsonThermometerWeakLongReading.original (m:=m) X form rem (ζ:=ζ) s r x U]
  intro w hw
  exact ⟨(pay w hw).1,(pay w hw).2,fun y hy rate=>
    WilsonThermometerWeakLongOccurrences.priced X form rem q low hy rate (ζ:=ζ) s r x w hw⟩

end YM.Integration.WilsonThermometerWeakOriginalShelves
end

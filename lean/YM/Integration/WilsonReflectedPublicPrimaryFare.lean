import YM.Integration.WilsonReflectedPublicOrientedCoefficient
/-! The original rotated field coordinate is paid on the same period as its signed residual. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicPrimaryFare
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Trace.Physical.Germ
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {d N p k:ℕ}
local notation "F" => R.family.labels.level d
local notation "P" => R.family.path.rep N p k
local notation "B₀" => WilsonThermometerOffsetLedger.cash R

theorem raw (home:Opened R.family d k p) (live:k≤N)
    (q:Coefficient (F) (R.family.side k p)) {κ B:ℝ} (form:q.Format 0 R.family.params (P))
    (paid:q.remBound 0 (P) κ B) (v:Palette R.family d)
    (head:Germ.projection (F) R.family.params (P).p.threshold 0 q = v (primaryLetter d)):
    (F).coeffSize q.x ≤ size v + B := by
  have dims:=dimensions d N p k R.makes home.post live
  let u:(F).Coeff:=v (primaryLetter d)
  have su:(F).coeffSize u ≤ size v := by
    rw [bill_group]
    exact Finset.single_le_sum (fun i _=>Work.G08.size_nonneg (R.family.labels.level (kept i)) (v i))
      (Finset.mem_univ (primaryLetter d))
  have cap:= (germ_close (F) R.family.params).choose_spec.2 (P) q form paid dims.1 dims.2
  rw [head] at cap
  let Cℓ:=((F).extra+1:ℕ)
  let t:ℝ:=(germ_close (F) R.family.params).choose
  have tpos:0≤t:= (germ_close (F) R.family.params).choose_spec.1.le
  have cn:0≤(Cℓ:ℝ):=Nat.cast_nonneg _
  have budget:(P).p=plank R.family k := (R.makes.wilson.represents N p k live).vac
  let a:ℝ:=(Cℓ:ℝ)*t*Germ.wraps (P).p (R.family.side k p)
  have an:0≤a:=mul_nonneg (mul_nonneg cn tpos) (Real.exp_pos _).le
  have little:a*stock R.family k<1/4 := by
    dsimp only [a]; rw [budget]; exact home.small
  have a1:a≤1:=by
    have havePay:a≤a*stock R.family k:=le_mul_of_one_le_right an (R.family.path.levels.params k).columns_ge
    linarith
  obtain ⟨x,z,tab,spend⟩:=rem_tabs.mp paid
  have Bn:0≤B:=(add_nonneg tab.first tab.second).trans spend
  have h:(F).coeffSize (q.x-u)≤a*B:= (size_le_norm (F) _).trans
    ((mul_le_mul_of_nonneg_left ((norm_sub_rev q.x u).le.trans cap) cn).trans_eq (by dsimp [a,Cℓ,t]; ring))
  calc
    _ = (F).coeffSize (u+(q.x-u)):=by congr 1; abel
    _ ≤ (F).coeffSize u+(F).coeffSize (q.x-u):=Size.add (F) _ _
    _ ≤ _ := add_le_add su (h.trans (mul_le_of_le_one_left Bn a1))

theorem original {V:Sight R.family d p}{r:Emblems R.family d}
    (z:Site (R.family.side N p)) (s:Motion) (c:Site (R.family.side k p)) (hk:k≤N)
    (home:Opened R.family d k p) (y:Palette R.family d)
    (enrolled:Enrolled R.makes R.doors B₀ k N p d (digits R N p z) V r):
    let o:=point R z s c k
    let Z:=marked R z s c V r y k
    let κ:=kappa R.family.path k
    let τ:=turnCost (P).p.order (P).p.power
    ∃ q : Coefficient (F) (R.family.side k p),
      q.Format o R.family.params (P) ∧
      (F).coeffSize q.x ≤ orbitCost (F)*(1+B₀ d k)*size y ∧
      (∃a b:ℝ,a+b≤B₀ d k*size y ∧ Tab q o (P) κ (τ*a) b) ∧
      q.remBound o (P) κ (τ*(B₀ d k*size y)) ∧ Z.2.1=q.exponentialEntry o (R.family.localSection d) (P) ∧
      profile (P).activities Z.2.2=profile (P).activities q.forced ∧
      q.density o (R.family.localSection d) (P)=Z.1 := by
  intro o Z κ τ
  obtain ⟨X,fmt,fee,head,_,read⟩:=WilsonThermometerWeakReflectedRows.master R z hk y enrolled
  let π:=Classical.choice ((R.makes.wilson.represents N p k hk).good.labels.moves s.1 o)
  have hn:2≤(R.family.side k p).val := (by decide : 2≤4).trans (Next.Foundations.actual_side_ge R.family.S k p)
  have paid:=WilsonReflectedPublicOrientedCoefficient.posted s o π X hn (R.makes.sections d) fmt fee (read s c)
  refine ⟨_,paid.1,?_,paid.2.2⟩
  rw [paid.2.1]
  exact (patch_cost (F) s X.x).trans ((mul_le_mul_of_nonneg_left (raw R home hk X fmt fee y head)
    (zero_le_one.trans (orbitCost_one_le (F)))).trans_eq (by ring))

end YM.Integration.WilsonReflectedPublicPrimaryFare
end

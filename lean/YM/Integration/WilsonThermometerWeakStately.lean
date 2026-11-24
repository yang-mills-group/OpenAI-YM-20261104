import YM.Integration.WilsonThermometerReflectedRoster
import YM.MergeProof.North.Sprite

/-! Each originally addressed arm before the replica capture, including the
scalar of the deposited Tale in its own physical marker radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakStately
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerReflectedTrajectory
open scoped Classical Topology
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {N p k:ℕ} {I:Type}
open WilsonThermometerReflectedRoster
variable (d:I→ℕ) (z:I→Site (R.family.side N p)) (s:I→Motion) (c:I→Site (R.family.side k p))
  (y:(i:I)→Palette R.family (d i)) (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i))
local notation "A" => R.alloy.B.a
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "O" => WilsonThermometerOwnOffsetJoint.origins R (fun i=>endpoint R (z i) (s i) (c i))
local notation "Q" => (fun j i=>marked R (z i) (s i) (c i) (V i) (r i) (y i) j)
local notation "f" => (fun j i=>(Q j i).2.1)
local notation "g" => (fun j i=>(Q j i).2.2)


def arms (hk:k≤N) (t:ℕ) : Prop :=
  ∀ i:I,MergeProof.Stately R.family.path (far A) k N p (fun j=>O j i) (radius R t k)
    (fun j=>f j i) (fun j=>g j i) (source R d z s c y r hk i) R.doors
theorem admitted (simple:G.Simple) (hk:k≤N)
    (H : ∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i))
    (aw : ∀ i,Awake (C:=R.family) R.doors B k (d i)) {u:ℝ}
    (test : ∀ i,Cap (d i+2) (line (primaryLetter (d i))) u) {t:ℕ}
    (upper : ∀ i,radius R t k N*(‖factor R k N (d i)‖*(u*size (finer (r i) hk (y i))*
      pricesTop (fly A) (far A) N (d i))) ≤ far A N)
    (lower : ∀ i j (hj:k≤j) (_:j<N),2*radius R t k (j+1)*charge R (r i) (y i) hj u ≤ 1) :
    arms R d z s c y V r hk t := by
  intro i
  have posEq (j:ℕ) (hj:k≤j) (hn:j≤N) : O j i=point R (z i) (s i) (c i) j := parent R _ _ _ hj hn
  have starts (e:ℕ) (he:e≤d i) := ((aw i).post e he).trans hk
  have top := WilsonThermometerReflectedTrajectory.upper R (z i) (s i) (c i) (y i) (H i) simple hk starts (test i)
  have safe (j:ℕ) (hj:k≤j) (hn:j≤N) := WilsonThermometerReflectedTrajectory.live R (z i) (s i) (c i) (y i) (H i) hj hn
  have next (j:ℕ) (hj:k≤j) (hn:j<N) := WilsonThermometerReflectedTrajectory.paid R (z i) (s i) (c i) (y i)
    (H i) (aw i) hj hn (test i)
  refine ⟨fun j hj hn=>(safe j hj hn).normK,?_,?_,?_,?_⟩
  · intro U
    exact (congrFun (WilsonThermometerReflectedTrajectory.written R (z i) (s i) (c i) (y i) (H i) hk starts) U).symm.trans
      ((congrFun (safe N hk le_rfl).read U).symm)
  · obtain ⟨F,hF,shown⟩ := top.2
    exact ⟨F,_,(posEq N hk le_rfl).symm ▸ hF,upper i,shown.symm⟩
  · intro j hj hn
    obtain ⟨S,hs,C,hC,pf⟩ := (next j hj hn).pays
    have half : radius R t k (j+1)*charge R (r i) (y i) hj u≤1 := by
      nlinarith only [lower i j hj hn,mul_nonneg (radius_pos R t k (j+1) (hj.trans j.le_succ)).le (next j hj hn).nonneg]
    rw [←posEq _ hj hn.le,←posEq _ (hj.trans j.le_succ) hn] at pf
    exact ⟨S,C,_,_,hs,lower i j hj hn,half,(mul_le_mul_of_nonneg_left hC (radius_pos R t k (j+1) (hj.trans j.le_succ)).le).trans half,pf⟩
  intro j hj hn
  have step := (next j hj hn).exactStep
  rw [one_smul] at step
  exact (safe j hj hn.le).read.trans (step.trans (congrArg ((R.family.path.levels.clock.op j p).push _)
    (safe (j+1) (hj.trans j.le_succ) hn).read.symm))
theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D:ℕ) :
    ∃ t ≥ D+3,∀ᶠ k:ℕ in atTop, ∀ p N (hk:k≤N) (I:Type) [Fintype I] [DecidableEq I]
      (d:I→ℕ) (_:∀ i,d i≤D) (z:I→Site (R.family.side N p))
      (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i))
      (_:∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i))
      (s:I→Motion) (c:I→Site (R.family.side k p)),
      ∀ (y:(i:I)→Palette R.family (d i)), (∀ i,size (y i)≤1) →
        arms R d z s c y V r hk t := by
  choose a pos caps using fun e : Fin (D+1)=>Cap.cost (line (primaryLetter e.val)) (e.val+2)
  let u : ℝ := 1+∑ e,a e
  have nonneg : 0≤∑ e,a e := Finset.sum_nonneg (fun e _=>(pos e).le)
  have up : 0<u := by dsimp [u];linarith
  have covered (e:ℕ) (he:e≤D) : Cap (e+2) (line (primaryLetter e)) u := by
    let l : Fin (D+1) := ⟨e,by omega⟩
    have c := Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(pos j).le) (Finset.mem_univ l)
    exact (caps l).increase (by dsimp [u];linarith)
  obtain ⟨t,dt,starts⟩ := Many.startPay (C:=R.family) simple D u up
  obtain ⟨k₀,starts⟩ := eventually_atTop.mp starts
  have awake : ∀ᶠ k:ℕ in atTop,∀ e:Fin (D+1),Awake (C:=R.family) R.doors B k e.val :=
    Filter.eventually_all.mpr fun e=>(WilsonThermometerOffsetLedger.original R simple shop e.val).mono fun _ h=>h.1
  have grow := Many.beta_le' (C:=R.family) simple
  refine ⟨t,dt,?_⟩
  filter_upwards [eventually_ge_atTop k₀,WilsonThermometerOwnOffsetRadii.paid R simple (D+3) t,
    awake,Many.theta_up (C:=R.family) (max 1 (2*u)) simple] with k late purse gates hot p N hk I _ _ d cap z V r H s c y small
  have gate (i:I) : Awake (C:=R.family) R.doors B k (d i) := gates ⟨d i,by have:=cap i;omega⟩
  have wallet (i:I) (j:ℕ) (hj:k≤j) :
      radius R t k j*(span R k j)^(d i+3)*β j^t ≤ 1 := by
    have lower := pow_le_pow_right₀ (span_one R hj) (show d i+3≤D+3 by have:=cap i;omega)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lower (radius_pos R t k j hj).le)
      (pow_nonneg (WardBin.hot _ _).le t)).trans (purse j hj)
  have last := starts N (late.trans hk)
  apply admitted R d z s c y V r simple hk H gate (fun i=>covered (d i) (cap i))
  · exact fun i=>WilsonThermometerOwnOffsetInvoice.top R (H i) (y i) (small i) up hk ⟨last.1,last.2 (d i) (cap i)⟩ (wallet i N hk)
  intro i j hj hn
  let X := span R k (j+1)
  let w := radius R t k (j+1)
  let b := β (j+1)
  have hkn := hj.trans j.le_succ
  have warm : max 1 (2*u) ≤ b := hot.trans (grow hkn)
  have fee : 2*u ≤ b^t := ((le_max_right 1 _).trans warm).trans
    (by simpa only [pow_one] using (pow_le_pow_right₀ ((le_max_left 1 _).trans warm) (show 1≤t by omega)))
  have smallcost := adjacent R (H i) (y i) (small i) up.le hj hn
  have wpos := (radius_pos R t k (j+1) hkn).le
  calc 2*w*charge R (r i) (y i) hj u ≤ 2*w*(X^(d i+3)*u) :=
          mul_le_mul_of_nonneg_left smallcost (by positivity : 0 ≤ 2*w)
       _ = w*X^(d i+3)*(2*u) := by ring
       _ ≤ w*X^(d i+3)*b^t := mul_le_mul_of_nonneg_left fee (mul_nonneg wpos (pow_nonneg (span_pos R k (j+1)).le _))
       _ ≤ 1 := wallet i (j+1) hkn

end YM.Integration.WilsonThermometerWeakStately
end

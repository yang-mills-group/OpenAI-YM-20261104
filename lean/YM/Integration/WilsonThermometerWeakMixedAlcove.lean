import YM.Integration.WilsonThermometerWeakMixedBoard
import YM.RG05Readout.Capture.Pantry

/-! The last separated charged program and its full original geometric return on one physical step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedAlcove
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "d" => WilsonThermometerFundedWeakCells.degree
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "slots" => (Stock.census (Fin 3))

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:Storage R.family R.doors) (t:ℕ) (ht:9 ≤ t) :
    ∀ᶠ w:ℕ in atTop,∀ m N p (wm:w ≤ m) (edge:m+1 < N) (o:Fin 3 → Site (R.family.side N p))
      (V:(i:Fin 3) → Sight R.family (d i) p) (Q:(i:Fin 3) → Emblems R.family (d i))
      (_:∀ i,Enrolled R.makes R.doors (B) w N p (d i) (digits R N p (o i)) (V i) (Q i))
      (y:(i:Fin 3) → Palette R.family (d i)),
      let z := fun i=>WilsonThermometerMarchSource.reduce (y i)
      let raw := fun j i=>state (k:=w) R (V i) (Q i) (z i) (o i) j
      let Ψ := R.family.path.rep N p (m+1)
      let o₁ := WilsonThermometerOwnOffsetJoint.origins R o (m+1)
      let kN : w ≤ N := by omega
      let X := WilsonThermometerIntrinsicRoster.density R d o z Q slots kN edge.le
      WilsonThermometerIntrinsicRoster.filed R d o z V Q slots kN t → ∀ D:ℕ,
      (∀i i':Fin 3,i ≠ i'→D*(4*Ψ.p.B+2)+2*Ψ.p.B < separation (o₁ i) (o₁ i')) →
      ∃ a f Z, Coursework R.family.path (apron (A)) (R.doors N p m (by omega)) (renal (A) m) a f ∧
        f ≤ 1/2 ∧
        MenuBoard Ψ (liveRow (raw (m+1))) Z (o₁ ∘ Prod.fst)
          (fun _=>radius R t w (m+1)) (((A).budget (m+1)).supportExponent-1) 1 ∧
        Alcove (R.family.path.rep N p m) (liveRow (raw m))
          (((A).clock.op m p).push Ψ.beta Z)
          (((A).clock.op m p).ratio.parent ∘ (o₁ ∘ Prod.fst)) (fun _=>renal (A) m * radius R t w (m+1))
          f (renal (A) m) (1/2) ∧
        (∀ U,specialize slots ((Real.exp (-(D:ℝ)):ℝ):ℂ) (Z U)=X U) ∧
        (∀ U,specialize slots 0 (Z U)=restore Ψ (fun i=>(raw (m+1) i).2.1)
          (fun i=>profile Ψ.activities (raw (m+1) i).2.2)
          (0:Support (R.family.side (m+1) p) → Config G (R.family.side (m+1) p) → Poly slots) 0 U) := by
  choose a pos caps using fun i:Fin 3=>Cap.cost (line (primaryLetter (d i))) (d i+2)
  let u:ℝ:=1+∑ i,a i
  have up:0 < u:=by dsimp [u]; linarith [Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(pos i).le)]
  have test (i:Fin 3):Cap (d i+2) (line (primaryLetter (d i))) u := by
    apply (caps i).increase
    have c:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(pos j).le) (Finset.mem_univ i)
    dsimp [u];linarith
  have awake : ∀ᶠ w:ℕ in atTop,∀ i:Fin 3,Awake (C:=R.family) R.doors (B) w (d i) :=
    Filter.eventually_all.mpr fun i=>(WilsonThermometerOffsetLedger.original R simple shop (d i)).mono fun _ h=>h.1
  filter_upwards [WilsonThermometerWeakMixedBoard.original R simple shop stock t ht,awake,WilsonThermometerOwnOffsetRadii.paid R simple 9 t,
    Many.theta_up (C:=R.family) (max 1 (2*u)) simple,(A).fits.deep.eventually_ge_atTop 4] with w bankPaid aw capital hot four m N p wm edge o V Q track y
  dsimp only
  let z:=fun (i:Fin 3)=>WilsonThermometerMarchSource.reduce (y i)
  let raw:=fun (j:ℕ) (i:Fin 3)=>state (k:=w) R (V i) (Q i) (z i) (o i) j
  let o₁:=WilsonThermometerOwnOffsetJoint.origins R o (m+1)
  let hN:w ≤ N:=by omega
  let charge₁:=fun (i:Fin 3)=>charge R (Q i) (z i) wm u
  intro bank D far
  obtain ⟨a,f,lab⟩:=stock.exactMoon.days N p m (by omega)
  have course:Coursework R.family.path (apron (A)) (R.doors N p m (by omega)) (renal (A) m) a f:=
    ⟨lab.2,lab.1⟩
  have walk (i:Fin 3):Ride ((A).clock.op m p) (o₁ i) (((A).clock.op m p).ratio.parent (o₁ i))
      (R.doors N p m (by omega)) 1 (raw (m+1) i) (raw m i) (charge₁ i) := by
    rw [WilsonThermometerOwnOffsetGeometry.parent R o (show m < N by omega) i]
    exact WilsonThermometerOwnOffsetNectar.paid R (track i) (aw i) wm (by omega) (z i) (test i)
  have occ {n:Side} (sites:Fin 3 × Bool → Site n) : Occupancy sites (apron (A) m) := by
    intro x
    refine (Finset.card_le_univ _).trans ?_
    have four' : 4 ≤ (A).clock.J (m+1) := four.trans ((A).fits.mono (show w ≤ m+1 by omega))
    change Fintype.card (Fin 3×Bool) ≤ (((A).clock.J (m+1))+2)*(R.family.S.block m).val^4
    have h:=one_le_pow₀ (show 1 ≤ (R.family.S.block m).val from (R.family.S.block m).property) (n:=4)
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] using
      (show 3*2 ≤ _ from (show 3*2 ≤ ((A).clock.J (m+1))+2 by omega).trans (Nat.le_mul_of_pos_right _ (by omega)))
  have home:=wm.trans m.le_succ
  have warm:= hot.trans (Many.beta_le' (C:=R.family) simple home)
  have fee:2*u ≤ β (m+1)^t := ((le_max_right 1 _).trans warm).trans
    (by simpa only [pow_one] using (pow_le_pow_right₀ ((le_max_left 1 _).trans warm) (show 1 ≤ t by omega)))
  have costs (i:Fin 3):2*radius R t w (m+1)*charge₁ i ≤ 1 := by
    have di : d i+3 ≤ 9 := by fin_cases i <;> decide
    have lower:=pow_le_pow_right₀ (span_one R home) di
    have bill:=capital (m+1) home
    have pocket:radius R t w (m+1)*(span R w (m+1))^(d i+3)*β (m+1)^t ≤ 1 :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lower (radius_pos R t w (m+1) home).le)
        (pow_nonneg (WardBin.hot _ _).le t)).trans bill
    have small:=adjacent R (track i) (z i) (WilsonThermometerMarchSource.small _) up.le wm (show m < N by omega)
    let w₁:=radius R t w (m+1)
    let a₁:=span R w (m+1)
    have wp:0 ≤ w₁:=(radius_pos R t w (m+1) home).le
    calc 2*w₁*charge₁ i ≤ 2*w₁*(a₁^(d i+3)*u) := mul_le_mul_of_nonneg_left small (by positivity)
       _ = w₁*a₁^(d i+3)*(2*u) := by ring
       _ ≤ w₁*a₁^(d i+3)*(β (m+1))^t := mul_le_mul_of_nonneg_left fee (mul_nonneg wp (pow_nonneg (span_pos R w (m+1)).le _))
       _ ≤ 1 := pocket
  obtain ⟨Z,board,rep,erased⟩:= bankPaid m N p wm edge o V Q track y bank D far
  have o₂ := ((A).clock.op m p).ratio.parent ∘ (o₁ ∘ (Prod.fst:Fin 3×Bool → Fin 3))
  have cap := course.plates R.makes.wilson (show m < N by omega) board
    (show ((A).budget (m+1)).supportExponent-4 ≤ ((A).budget (m+1)).supportExponent-1 by linarith)
    (ν:=fun _=>1) (fun _=>by simp) (fun _=>radius_pos R t w (m+1) home)
    (WilsonMixedTaggedRide.doubled walk) (occ _) (occ _)
    (WilsonMixedTaggedRide.room costs)
  have stake:=course.poses.stakes.1
  have costPos : 0 ≤ (apron (A) m:ℝ)*siteFactor ((A).budget m).B*renal (A) m := by
    exact mul_nonneg (mul_nonneg (by positivity) (by unfold siteFactor;positivity)) course.poses.hats.1.le
  have toll : (1:ℝ) ≤ (((A).budget m).B+((A).budget m).B+1:ℕ)^4 := by
    exact_mod_cast (one_le_pow₀ (show 1 ≤ ((A).budget m).B+((A).budget m).B+1 by omega) (n:=4))
  have small : f ≤ 1/2 := by
    by_cases hp : 0 ≤ f
    · have hs:=mul_le_mul_of_nonneg_right toll (add_nonneg hp costPos)
      simp only [one_mul] at hs
      linarith [hs.trans stake]
    · linarith
  refine ⟨a,f,Z,course,small,board,?_,rep,erased⟩
  simpa only [inv_one,one_smul] using cap

end YM.Integration.WilsonThermometerWeakMixedAlcove
end

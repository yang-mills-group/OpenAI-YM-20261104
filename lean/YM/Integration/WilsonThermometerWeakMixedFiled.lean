import YM.Integration.WilsonThermometerWeakMixedBoard
import YM.Integration.WilsonThermometerWeakMixedCapture

/-! The genuine last-separated three-source board issued with its own original Wilson cluster receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedFiled
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open MergeProof.Ribbons MergeProof.Float MergeProof.Ribbon Pressure
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "d" => WilsonThermometerFundedWeakCells.degree
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "slots" => (Stock.census (Fin 3))

theorem original {J:Type} [Fintype J] [DecidableEq J] (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:Storage R.family R.doors) (cater:Cater R.family R.doors) (t:ℕ) (ht:9 ≤ t) :
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
      ∃ Z, MenuBoard Ψ (liveRow (raw (m+1))) Z (o₁ ∘ Prod.fst)
          (fun _=>radius R t w (m+1)) (((A).budget (m+1)).supportExponent-1) 1 ∧
        (∀ U,specialize slots ((Real.exp (-(D:ℝ)):ℝ):ℂ) (Z U)=X U) ∧
        (∀ U,specialize slots 0 (Z U)=restore Ψ (fun i=>(raw (m+1) i).2.1)
          (fun i=>profile Ψ.activities (raw (m+1) i).2.2)
          (0:Support (R.family.side (m+1) p) → Config G (R.family.side (m+1) p) → Poly slots) 0 U) ∧
        ∀ (L:Fibers (Fin 3) J) (H l:ℕ),0<H → (∀ v,(L.contents v).card≤H) →
          let Θ:=R.family.path.rep N p m
          let o₂:=((A).clock.op m p).ratio.parent ∘ o₁
          (∀ i,coverNumber Θ.p.B ({o₂ (L.twig (L.bunch i)),o₂ i}:Support (R.family.side m p))≤l) →
          ∀ h:ℂ,‖h‖≤1 →
            let W:=((A).clock.op m p).push Ψ.beta (fun U=>specialize slots h (Z U))
            let fees:=WilsonThermometerWeakMixedGrouping.radius L Θ H l (renal (A) m)
              (fun _=>renal (A) m * radius R t w (m+1))
            ∃ g:J → Config G (R.family.side m p)→ℂ,∃ K:J→ℕ → Config G (R.family.side m p)→ℂ,
              Served Θ g (fun v=>profile Θ.activities (K v)) (fun U=>Fibers.reap L (W U))
                (o₂ ∘ L.twig) fees Θ.p.supportExponent 1 ∧
              ∀ v,Dominated (K v) ∧ Blade Θ (o₂ (L.twig v)) (g v) (profile Θ.activities (K v))
                0 (4*(1/fees v)) := by
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
    Many.theta_up (C:=R.family) (max 1 (2*u)) simple,(A).fits.deep.eventually_ge_atTop 4,eventually_ge_atTop (1:ℕ)] with w bankPaid aw capital hot four one m N p wm edge o V Q track y
  dsimp only
  let z:=fun (i:Fin 3)=>WilsonThermometerMarchSource.reduce (y i)
  let raw:=fun (j:ℕ) (i:Fin 3)=>state (k:=w) R (V i) (Q i) (z i) (o i) j
  let o₁:=WilsonThermometerOwnOffsetJoint.origins R o (m+1)
  let hN:w ≤ N:=by omega
  let charge₁:=fun (i:Fin 3)=>charge R (Q i) (z i) wm u
  intro bank D far
  have walk (i:Fin 3):Ride ((A).clock.op m p) (o₁ i) (((A).clock.op m p).ratio.parent (o₁ i))
      (R.doors N p m (by omega)) 1 (raw (m+1) i) (raw m i) (charge₁ i) := by
    rw [WilsonThermometerOwnOffsetGeometry.parent R o (show m < N by omega) i]
    exact WilsonThermometerOwnOffsetNectar.paid R (track i) (aw i) wm (by omega) (z i) (test i)
  have occ {n:Side} (sites:Fin 3 → Site n) : Occupancy sites (apron (A) m) := by
    intro x
    refine (Finset.card_le_univ _).trans ?_
    have four' : 4 ≤ (A).clock.J (m+1) := four.trans ((A).fits.mono (show w ≤ m+1 by omega))
    change Fintype.card (Fin 3) ≤ (((A).clock.J (m+1))+2)*(R.family.S.block m).val^4
    have h:=one_le_pow₀ (show 1 ≤ (R.family.S.block m).val from (R.family.S.block m).property) (n:=4)
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] using
      (show 3 ≤ _ from (show 3 ≤ ((A).clock.J (m+1))+2 by omega).trans (Nat.le_mul_of_pos_right _ (by omega)))
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
  refine ⟨Z,board,rep,erased,?_⟩
  intro L H l order enough close h small
  cases m with
  | zero=>omega
  | succ j=>
    exact WilsonThermometerWeakMixedCapture.original R cater (show j+1 < N by omega)
      L H l order enough _ _ _ _ _ Z board (fun _=>radius_pos R t w _ home) walk
      (occ _) (occ _) costs close h small

end YM.Integration.WilsonThermometerWeakMixedFiled
end

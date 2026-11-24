import YM.Integration.WilsonThermometerWeakMixedFaces

/-! The first-separation mixed error and the exact cutoff-born thermometer, on every earlier held field of one physical Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedMeasured
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

theorem joined {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F:History G) (N p n j:ℕ) (hn:j ≤ n) (f:Config G (F.S.side n p)→Y) {i:ℕ} (hi:i ≤ j) :
    gust F N p j (gust F N p n f j hn) i hi = gust F N p n f i (hi.trans hn) := by
  induction hi using Nat.decreasingInduction with
  | self=>simp only [gust_base]
  | of_succ k h IH=>rw [gust_step F N p j _ h,gust_step F N p n _ (h.trans_le hn),IH]

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
      let E:=restore Ψ (fun i=>(raw (m+1) i).2.1)
        (fun i=>profile Ψ.activities (raw (m+1) i).2.2)
        (0:Support (R.family.side (m+1) p) → Config G (R.family.side (m+1) p) → Poly slots) 0
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
        ∀ i (hi:i ≤ m+1) (U:Config G (R.family.side i p)) (s:(slots).Mode),
          let earlier:=gust R.family.path N p (m+1) Z i hi U
          let actual:=WilsonThermometerIntrinsicRoster.density R d o z Q slots kN (hi.trans edge.le) U
          let one:=gust R.family.path N p (m+1) E i hi U
          let vacuum:=((R.family.path.rep N p i).eval U:ℂ)
          specialize slots ((Real.exp (-(D:ℝ)):ℝ):ℂ) earlier=actual ∧
          specialize slots 0 earlier=one ∧
          ‖(actual.part s-one.part s)/vacuum‖ ≤
            (Real.exp (-(D:ℝ))/‖vacuum‖)*∑ j:(census slots).Mode,
              if s=WilsonMixedTaggedEntries.base j then ‖earlier.part j‖ else 0 := by
  filter_upwards [WilsonThermometerWeakMixedAlcove.original R simple shop stock t ht] with w paid
  intro m N p wm edge o V Q tr y
  dsimp only
  intro funded D far
  obtain ⟨a,f,Z,course,small,board,cap,full,zero⟩:=paid m N p wm edge o V Q tr y funded D far
  refine ⟨a,f,Z,course,small,board,cap,?_⟩
  intro i hi U s
  let δ:=Real.exp (-(D:ℝ))
  have hp : 0 ≤ δ := (Real.exp_pos _).le
  have hs : δ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have normδ : ‖(δ:ℂ)‖ = δ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  have pp := congrFun (WilsonThermometerWeakMixedFaces.transported slots R.family.path (N:=N) (p:=p) (j:=m+1)
    (δ:ℂ) Z board.cleared hi) U
  have p0 := congrFun (WilsonThermometerWeakMixedFaces.transported slots R.family.path (N:=N) (p:=p) (j:=m+1)
    0 Z board.cleared hi) U
  dsimp only [δ] at pp
  rw [funext full] at pp
  rw [funext zero] at p0
  unfold WilsonThermometerIntrinsicRoster.density at pp
  rw [joined] at pp
  refine ⟨pp.symm,p0.symm,?_⟩
  unfold WilsonThermometerIntrinsicRoster.density
  rw [pp,p0,norm_div]
  have fee:=WilsonThermometerWeakMixedFaces.bill slots (z:=(δ:ℂ)) (normδ.trans_le hs)
    (gust R.family.path N p (m+1) Z i hi U) s
  rw [normδ] at fee
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right fee (norm_nonneg _)

end YM.Integration.WilsonThermometerWeakMixedMeasured
end

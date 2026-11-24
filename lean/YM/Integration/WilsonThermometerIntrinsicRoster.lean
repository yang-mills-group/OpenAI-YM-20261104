import YM.Integration.WilsonThermometerOwnOffsetRoster

/-! Each marked leg has its own engineering grade, palette and measured
ancestral circuit. They share one signed Wilson history and one price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerIntrinsicRoster
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open scoped Classical Topology
set_option quotPrecheck false
variable {G : Gauge} (R : Run G) {N p k : ℕ} {I : Type} (d : I → ℕ)
variable (z : I → Site (R.family.side N p)) (y : (i:I) → Palette R.family (d i))
  (V : (i:I) → Sight R.family (d i) p) (r : (i:I) → Emblems R.family (d i))
local notation "A" => R.alloy.B.a
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "O" => WilsonThermometerOwnOffsetJoint.origins R z
local notation "Q" => (fun j i=>state (k:=k) R (V i) (r i) (y i) (z i) j)
local notation "f" => (fun j i=>(Q j i).2.1)
local notation "g" => (fun j i=>(Q j i).2.2)

def source (hk:k≤N) (i:I) :=
  WilsonThermometerOwnOffsetNectar.birth R
    ((R.family.factory (d i) N p).terminal (finer (r i) hk (y i) (primaryLetter (d i)))) k (z i)

variable [Fintype I] [DecidableEq I]
def density (names:Census I) (hk:k≤N) {j:ℕ} (hn:j≤N) :=
  gust R.family.path N p N (Accent.birth names (R.family.path.rep N p N) (source R d z y r hk)) j hn

def filed (names:Census I) (hk:k≤N) (t : ℕ) : Prop :=
  ∀ j (_:k≤j) (hn:j≤N),
    Integrable (density R d z y r names hk hn) (prior G _) ∧
    (∀ i,(fun U=>(density R d z y r names hk hn U).part (names.fire i))=
      Accent.manifest R.family.path p N f g j i) ∧
    Served (R.family.path.rep N p j) (f j) (Accent.tapes R.family.path p N g j)
      (density R d z y r names hk hn) (O j) (fun _=>radius R t k j) (topPitch R.family.path N j) 1

theorem admitted (simple:G.Simple) (hk:k≤N) (names:Census I)
    (room : ∀ i i':I,i≠i' → (R.family.path.levels.budget k).B^2 < separation (O k i) (O k i'))
    (H : ∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i))
    (aw : ∀ i,Awake (C:=R.family) R.doors B k (d i)) {u : ℝ}
    (test : ∀ i,Cap (d i+2) (line (primaryLetter (d i))) u)
    {t : ℕ}
    (upper : ∀ i,radius R t k N*(‖factor R k N (d i)‖*(u*size (finer (r i) hk (y i))*
      pricesTop (fly A) (far A) N (d i))) ≤ far A N)
    (lower : ∀ i j (hj:k≤j) (_:j<N),2*radius R t k (j+1)*charge R (r i) (y i) hj u ≤ 1) :
    filed R d z y V r names hk t := by
  let joint := source R d z y r hk
  have geo := WilsonThermometerOwnOffsetGeometry.admitted R simple z t names room
  have arms (i:I) : Nectar R.family.path (far A) R.doors p N k O
      (fun j _=>radius R t k j) f g joint i := by
    have half (j : ℕ) (hj:k≤j) (hn:j<N) : radius R t k (j+1)*charge R (r i) (y i) hj u ≤ 1 := by
      have h := lower i j hj hn
      have hh := (WilsonThermometerOwnOffsetNectar.paid R (H i) (aw i) hj hn (y i) (test i)).nonneg
      nlinarith only [h,mul_nonneg (radius_pos R t k (j+1) (hj.trans j.le_succ)).le hh]
    have arm := WilsonThermometerOwnOffsetJoint.accepted (I:=Unit) R (fun _=>z i) (fun _=>y i)
      (fun _=>V i) (fun _=>r i) (fun _=>H i) (aw i) simple hk (fun j _=>radius R t k j)
      (test i) () (upper i) (lower i) half
    exact ⟨arm.stocked,arm.writes,arm.patent,arm.sways,arm.feeds⟩
  have hCont (i:I) : Continuous (joint i) := by
    change Continuous (fun U=>((R.family.S.a k:ℂ)^(d i)) • R.family.O N p _ (z i) U)
    exact (R.family.continuousO N p (d i) _ (z i)).const_smul ((R.family.S.a k:ℂ)^(d i))
  have actual : Continuous (R.family.path.rep N p N).eval := by
    have starts : (R.family.path.rep N p N).eval=bare (R.family.beta N p) := (R.makes.wilson.starts N p).2
    rw [starts];exact bare_cont _
  have initial : Integrable (Accent.birth names (R.family.path.rep N p N) joint) (prior G _) :=
    (hatCont R.family N p joint hCont actual names).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply sentry R.family.path (mutt A R.Q) (renal A) (far A) R.doors p N O (fun j _=>radius R t k j) f g joint
    R.makes.wilson hk geo (R.again simple).1.scrim.costs.night arms
  · intro j _ hn;exact gust_step _ _ _ _ _ hn
  · exact gust_base ..
  unfold density;rw [gust_base];exact initial

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D : ℕ) :
    ∃ t ≥ D+3,∀ᶠ k : ℕ in atTop, ∀ p N (hk:k≤N) (I : Type) [Fintype I] [DecidableEq I]
      (d : I→ℕ) (_:∀ i,d i≤D) (z:I→Site (R.family.side N p)),
      (∀ i i':I,i≠i' → (R.family.path.levels.budget k).B^2 <
        separation (WilsonThermometerOwnOffsetJoint.origins R z k i)
          (WilsonThermometerOwnOffsetJoint.origins R z k i')) →
      ∃ (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i)),
        (∀ i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀ (names:Census I) (y:(i:I)→Palette R.family (d i)), (∀ i,size (y i)≤1) →
          filed R d z y V r names hk t := by
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
    awake,Many.theta_up (C:=R.family) (max 1 (2*u)) simple] with k late purse gates hot p N hk I _ _ d cap z room
  have gate (i:I) : Awake (C:=R.family) R.doors B k (d i) := gates ⟨d i,by have:=cap i;omega⟩
  choose V r H using fun i:I=>enroll R.makes (gate i) hk (digits R N p (z i))
  refine ⟨V,r,H,?_⟩
  intro names y small
  have wallet (i:I) (j:ℕ) (hj:k≤j) :
      radius R t k j*(span R k j)^(d i+3)*β j^t ≤ 1 := by
    have lower := pow_le_pow_right₀ (span_one R hj) (show d i+3≤D+3 by have:=cap i;omega)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lower (radius_pos R t k j hj).le)
      (pow_nonneg (WardBin.hot _ _).le t)).trans (purse j hj)
  have last := starts N (late.trans hk)
  apply admitted R d z y V r simple hk names room H gate (fun i=>covered (d i) (cap i))
  · exact fun i=>top R (H i) (y i) (small i) up hk ⟨last.1,last.2 (d i) (cap i)⟩ (wallet i N hk)
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

end YM.Integration.WilsonThermometerIntrinsicRoster
end

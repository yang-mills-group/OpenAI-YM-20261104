import YM.Integration.WilsonThermometerWeakIssuedDetector

/-! Retain the individual grade price of the actual issued displaced field.
All copies use the same Wick-calibrated basis. The reconstruction holds for every
presentation of its actual signed transfer, including the presentation of the joint post. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFiledSalary
open Function Filter Set MeasureTheory RG RG12 Extra.Histories Lattice Wilson Source Labels
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerWeakBasisCalibration WilsonThermometerWeakPhysicalCombination
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "A" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem stake (exam:Tapes.Panel H) (v:(Rf).label d) (k N p:ℕ) (hk:k≤N) :
    let P:=(Rf).path.rep N p k
    let g:=GaugeScale Rf k N p
    let s:=clim (A) k
    let ξ:=exam.bag ((A).clock.J k)
    let F:=(Rf).labels.level d
    let x:=Price.weightTag Rf d (mag (A) ξ.band k) v
    2*F.coeffSize (F.scaled (P.p.threshold/g) x) ≤
      (2*2^leash F*F.coeffSize v)*bill (exam.arc*d+(leash F:ℝ)) s := by
  let F:=(Rf).labels.level d
  let q:=leash F
  let b:=exam.arc
  let γ:=b*d+(q:ℝ)
  have hb:0<b:=by have :=exam.huge;dsimp only [b];linarith only [this,Nat.cast_nonneg (α:=ℝ) H]
  intro P g s ξ F' x
  have ratio:P.p.threshold/g=(Price.shrink Rf k N p)⁻¹:=by
    change P.p.threshold/_=(_/(A).clock.threshold k)⁻¹
    rw [inv_div,show P.p.threshold=(A).clock.threshold k from ((R.makes.wilson.represents N p k hk).vac) ▸ rfl];rfl
  let a:=Price.shrink Rf k N p
  have az:0<a:=Price.shrink_pos Rf R.makes hk p
  let m:=(A).clock.monitor k
  have m1 : 1 ≤ m := Real.one_le_exp (sq_nonneg _)
  let ρ:=mag (A) b k
  have hρ:1≤ρ:=Real.one_le_rpow m1 hb.le
  let room:ℝ:=2*m
  have lens (i):‖F.scaled a⁻¹ (Price.weightTag Rf d ρ v) i‖≤room^q*ρ^d*‖v i‖:=by
    unfold Price.weightTag;simp only [Frame.scaled_apply,LinearMap.coe_mk,AddHom.coe_mk,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr az).le _),Real.norm_of_nonneg (zero_le_one.trans hρ)]
    rw [←mul_assoc];apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul ((pow_le_pow_left₀ (inv_pos.mpr az).le (Price.shrink_min Rf R.makes hk p) _).trans
      (pow_le_pow_right₀ (show 1≤room by dsimp only [room];linarith only [m1]) (Finset.le_sup (f:=fun i=>(F.grades i).2) (Finset.mem_univ i))))
      (pow_le_pow_right₀ hρ (F.bound i)) (pow_nonneg (zero_le_one.trans hρ) _) (pow_nonneg (by dsimp only [room];linarith only [m1]) _)
  have sum:F.coeffSize (F.scaled a⁻¹ (Price.weightTag Rf d ρ v))≤room^q*ρ^d*F.coeffSize v:=by
    unfold Frame.coeffSize;rw [Finset.mul_sum];exact Finset.sum_le_sum fun i _=>lens i
  change 2*F.coeffSize (F.scaled (P.p.threshold/g) (Price.weightTag Rf d (mag (A) ξ.band k) v))≤_
  rw [ratio,show ξ.band=b from exam.factor _]
  calc
    _ ≤ 2*(room^q*ρ^d*F.coeffSize v):=mul_le_mul_of_nonneg_left sum (by norm_num)
    _ = (2*2^q*F.coeffSize v)*bill γ s:=by
      dsimp only [room,ρ,γ];rw [mul_pow,show m=bill 1 s from fire_bill (A) k,mag_bill,bills,bills]
      rw [show clim (A) k=s from rfl,←overlap];ring_nf

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G)
    (exam:Tapes.Panel H) (dH:d≤H) (v:(Rf).label d):
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N),
    let P:=(Rf).path.rep N p k;let g:=GaugeScale Rf k N p;let s:=clim (A) k
    let ξ:=exam.bag ((A).clock.J k);let F:=(Rf).labels.level d;let b:=sizeQ Rf k
    let feed:=Price.weightTag Rf d (mag (A) ξ.band k) v
    ∃(K:Provision Rf d k N p (scouts Rf k) b)(wide:4*b≤wood (A) k),ξ.taylor+1≤P.p.order →
    ∀ (z:Site ((Rf).side N p)) (V:Sight Rf d p) (r:Emblems Rf d),
    Enrolled R.makes R.doors B k N p d (digits R N p z) V r →
    ∀ E:AtlasData G (Rf).S p,Hail Rf k p ξ.taylor E →
    ∃ (u:F.Coeff) (L:poly (Up Rf k p b)),
    let W:=sender K.length P.p.threshold g L;let y:=chunk (C:=Rf) (primaryLetter d) u
    size y≤bill (ξ.credit-1) s ∧ coin W≤bill ξ.credit s ∧
      coin W≤(2*bill (5/8) s)*((2*2^leash F*F.coeffSize v)*bill (exam.arc*d+(leash F:ℝ)) s) ∧ W.totalDegree≤ξ.taylor ∧ Spirit W ∧
    WilsonThermometerWeakGroupCoordinate.contracted R d wide E W=expose F feed ∧
    ∀ (Y:Coefficient F ((Rf).side k p)),V k y (line (primaryLetter d))=invoice Y 0 ((Rf).localSection d) P →
    ∀ U,Healthy (tau (A) k) (Spindle.patch b 0) U →
      ‖Y.exponentialEntry 0 ((Rf).localSection d) P U-signet 0 g W U‖≤bill (1/8-(ξ.taylor:ℝ)) s*size y:=by
  filter_upwards [WilsonThermometerWeakMeasuredBasis.original R simple shop S d exam.θ (dH.trans exam.enough),
    WilsonThermometerWeakDetectorStake.original R simple exam dH v,supports exam.θ Rf simple R.makes] with k basis prices gauge N p hk P g s ξ F b feed
  obtain ⟨K,wide,publish⟩:=basis N p hk
  refine ⟨K,wide,?_⟩
  intro deg z V r paid E hail
  have θ:ξ.taylor=exam.θ:=exam.stable _
  rw [θ] at deg hail
  obtain ⟨X,Q,filedX,terms,read⟩:=publish deg z V r paid
  let H' i:=sender K.length P.p.threshold g (Q i)
  obtain ⟨T,rent,hT⟩:=read E hail
  let h:=P.p.threshold/g
  let u:=T.symm (F.scaled h feed)
  let y:=chunk (C:=Rf) (primaryLetter d) u
  let L:=filed F Q u
  have h0:h≠0:=(div_pos P.p.threshold_pos (gauge N hk p).1).ne'
  have contract:=WilsonThermometerWeakPhysicalCombination.calibrated R wide E H' T rent h0 (fun i=>by obtain ⟨v,eq,see⟩:=hT i;exact ⟨v,eq.symm,see⟩) feed
  have full:F.coeffSize u≤bill (ξ.credit-1) s:=contract.1.trans (prices N p hk).1
  have field:sender K.length P.p.threshold g L=filed F H' u:=by
    simp only [L,filed,Spindle.sender,dustAt,map_sum,map_smul,H']
  have book:=stock F H' (fun i=>(terms i).1) (fun i=>(terms i).2.1) (fun i=>(terms i).2.2.1) u
  refine ⟨u,L,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [size_chunk];exact full
  · rw [field];exact book.1.trans ((prices N p hk).2 _ full)
  · rw [field]
    exact book.1.trans (mul_le_mul_of_nonneg_left (contract.1.trans (stake R exam v k N p hk)) (mul_nonneg (by norm_num) (Real.exp_pos _).le))
  · rw [field,θ];exact book.2.1
  · rw [field];exact book.2.2
  · rw [field];exact contract.2
  · intro Y eq U healthy;rw [field,θ,size_chunk]
    exact tested R V g H' X (fun i=>(filedX i).2.2) (fun i=>(terms i).2.2.2)
      u Y eq U healthy

end YM.Integration.WilsonAddressedWeakFiledSalary


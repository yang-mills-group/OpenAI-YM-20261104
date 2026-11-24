import YM.Integration.ManuscriptQLocalMarkedHeight

/-! The true complete marked height split after restoring the physical source normalization.
Every nonzero product takes its labels from disjoint, nonempty original modes. This
statement keeps the entire marked matrix and the original conditional wing tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedHeightTail
open Filter Function Finset Lattice RG Tree Pressure Pressure.Stores ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Next.Scheduling AnalyticBridge VerifiedReset
open MergeProof Marker Extra.Multi LocalLTE PhysicalNext.Repeat.Daisy
open scoped Classical Topology BigOperators

variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W x μ a:ℝ}
  {o:Target.Order G W} (H:Cash W x μ L Q o a T R)

theorem exceptional (ℓ:ℕ) (hβ:1≤betaF G x L)
    (hc:Height.grow G L x^ℓ≤Real.exp (Q.mark L μ x))
    (ht:Height.grow G L x^ℓ≤Real.exp (Q.ε*Pressure.Stores.till x))
    (z:H.fragrances) (h:Height.tiredN H ℓ z) : Height.grow G L x^ℓ≤Height.beaconN H ℓ z := by
  let D:=Height.grow G L x
  have hd:1≤D:=Real.one_le_rpow hβ (by norm_num)
  have e:1≤Real.exp (Q.ε*Height.depth H z):=Real.one_le_exp
    (mul_nonneg Q.usable.le (sum_nonneg fun i _=>H.positive_volume _))
  have m:0≤Q.mark L μ x:=H.laws.acquired.marked
  have r:1≤Real.exp (Q.mark L μ x*Height.overlap H z):=
    Real.one_le_exp (mul_nonneg m (Nat.cast_nonneg _))
  rcases h with h|h|h
  · exact (pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right (by positivity) r).trans
      (le_mul_of_one_le_right (by positivity) e))
  · exact hc.trans ((Real.exp_monotone (le_mul_of_one_le_right m (show (1:ℝ)≤Height.overlap H z by
      exact_mod_cast h))).trans ((le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hd)).trans
        (le_mul_of_one_le_right (by positivity) e)))
  · exact ht.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) r)))

section Material
variable {V ι:Type} [DecidableEq V] [Fintype V] [Fintype ι] {Γ:Marker.Census V}
  (M:ι→Menu.Hat Γ R)
private abbrev leaves (M:ι→Menu.Hat Γ R) := fun l=>(M l).M

abbrev Occ (z:Fan.Stars H (leaves M)) := (j:Option (Fin z.1.1)) × ↥((z.2 j).val : Finset ι)

def matrix (z:Fan.Stars H (leaves M)) : Poly Γ := ∏ v:Occ H M z,Menu.stamp (M v.2.val)

def phase (w:V→ℝ) (z:Fan.Stars H (leaves M)) : Poly Γ := ∏ v:Occ H M z,Menu.sing (M v.2.val) w

omit [Fintype ι] in
theorem occupied (z:Fan.Stars H (leaves M)) (u:Occ H M z→ℂ)
    (h:(∏v:Occ H M z,Poly.send (M v.2.val).s (u v))≠0) :
    Fintype.card (Occ H M z)≤Fintype.card V := by
  classical
  let F (v:Occ H M z):=Poly.send (M v.2.val).s (u v)
  have disj (i j:Occ H M z) (hn:i≠j):Disjoint (M i.2.val).s.val (M j.2.val).s.val := by
    by_contra hh
    have hij:j∈(Finset.univ:Finset (Occ H M z)).erase i:=Finset.mem_erase.mpr ⟨hn.symm,Finset.mem_univ _⟩
    have hz:F i*F j=0:=by
      ext s
      change (Poly.prod _ _).part s=0
      rw [Poly.cart]
      exact if_neg (fun hm=>hh hm.1)
    apply h
    change ∏v,F v=0
    rw [←Finset.mul_prod_erase Finset.univ F (Finset.mem_univ i),
      ←Finset.mul_prod_erase (Finset.univ.erase i) F hij,←mul_assoc,hz,zero_mul]
  choose mark hm using (fun i:Occ H M z=>(M i.2.val).shiny)
  apply Fintype.card_le_of_injective mark
  intro i k he
  by_contra hn
  exact Finset.disjoint_left.mp (disj i k hn) (hm i) (he ▸ hm k)

omit [Fintype V] in
private theorem factored {E:Type} (D:Finset E) (p:E→Menu.Hat Γ R) (w:V→ℝ) (hw:∀v,0<w v) :
    (∏i∈D,Menu.stamp (p i))=(∏i∈D,(Menu.sumFee (p i) w:ℂ)) • ∏i∈D,Menu.sing (p i) w := by
  classical
  induction D using Finset.induction_on with
  | empty=>simp
  | @insert i D h ih=>
    rw [Finset.prod_insert h,Finset.prod_insert h,Finset.prod_insert h,←Menu.purchase (p i) hw,
      ih,smul_mul_assoc,mul_smul_comm,smul_smul]

omit [Fintype V] [Fintype ι] in
theorem physical (w:V→ℝ) (hw:∀v,0<w v) (z:Fan.Stars H (leaves M)) :
    matrix H M z=(Captain.pearl z.1 (leaves M) (fun i=>Menu.sumFee (M i) w) z.2:ℂ) • phase H M w z := by
  rw [matrix,phase,factored _ _ w hw]
  congr 1
  have join (b:Finset ι):
      (∏i∈b.attach,(Menu.sumFee (M i.val) w:ℂ))=∏i∈b,(Menu.sumFee (M i) w:ℂ):=
    Finset.prod_attach b (fun i:ι=>(Menu.sumFee (M i) w:ℂ))
  simp [Occ,Captain.pearl,Fintype.prod_sigma]
  exact congrArg₂ (·*·) (join _) (Finset.prod_congr rfl (fun i _=>join _))

omit [Fintype V] [Fintype ι] in
theorem unit (w:V→ℝ) (hw:∀v,0<w v) (z:Fan.Stars H (leaves M)) :
    Poly.price w (phase H M w z)≤1 := by
  refine (Poly.multiple hw Finset.univ (fun v:Occ H M z=>Menu.sing (M v.2.val) w)).trans ?_
  exact Finset.prod_le_one (fun i _=>Poly.nonnegative hw _) (fun i _=>Menu.paid _ hw)

omit [Fintype V] [Fintype ι] in
theorem pearl_scale (w:ι→ℝ) (b:ℝ) (z:Fan.Stars H (leaves M)) :
    Captain.pearl z.1 (leaves M) (fun i=>b*w i) z.2 =
      b^(Fintype.card (Occ H M z))*Captain.pearl z.1 (leaves M) w z.2 := by
  rw [Fan.braceT (leaves M) H z (fun _=>b) w]
  simp [Captain.pearl,Occ,Fintype.card_sigma,Finset.prod_pow_eq_pow_sum]

variable {C d rv s A v₁ y B e:ℝ} {j k:ℕ} {χ:Push.SectorMeasure.Chi}
  (N:Captain H j C d rv s A v₁ y B e k χ)

theorem signed (n ℓ:ℕ) (w:V→ℝ) (hw:∀v,0<w v) (hβ:1≤betaF G x L)
    (hc:Height.grow G L x^ℓ≤Real.exp (Q.mark L μ x))
    (ht:Height.grow G L x^ℓ≤Real.exp (Q.ε*Pressure.Stores.till x))
    {u γ:ℝ}
    (bill:Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*
        Height.markU N (leaves M) (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M i) w) z n) γ u) :
    Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if Height.tiredN H ℓ z.1 then Poly.price w (matrix H M z)*Captain.wife N z.1 (leaves M) z.2 n else 0)
      γ (((betaF G x L)^2)^Fintype.card V*(Height.grow G L x^ℓ)⁻¹*u) := by
  classical
  let β:=betaF G x L
  let b:=β^2
  let g:=Height.grow G L x
  let r:=fun i=>Menu.sumFee (M i) w
  let r':=fun i=>β^(-(2:ℝ))*r i
  have hb:1≤b:=one_le_pow₀ hβ
  have bp:0<b:=zero_lt_one.trans_le hb
  have hh:1≤g:=Real.one_le_rpow hβ (by norm_num)
  have gp:0<g^ℓ:=pow_pos (zero_lt_one.trans_le hh) _
  have eβ:β^(-(2:ℝ))=b⁻¹:=by rw [Real.rpow_neg (zero_le_one.trans hβ)];norm_num [b,β]
  have r0 i:0≤r i:=Menu.timed _ hw
  have r1 i:0≤r' i:=mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hβ) _) (r0 i)
  let S':=fun z=>Fan.wagesZ (leaves M) H χ ℓ k r' N (fun _=>1) n z
  have paid:Ac.Hit (fun z:Fan.Stars H (leaves M)=>Captain.reachability z.1) (radiusB x) S' γ u:=
    Fan.ticketsT (leaves M) H χ ℓ k r' r1 N (fun _=>1) (fun _=>le_rfl) hβ n γ u bill
  have raw (z:Fan.Stars H (leaves M)):0≤Captain.wife N z.1 (leaves M) z.2 n:=
    mul_nonneg (pow_nonneg (by unfold March.shiftG;positivity) _)
      (Captain.fareV N z.1 (leaves M) z.2)
  have major (z:Fan.Stars H (leaves M)):0≤S' z:=
    Fan.roaring (leaves M) H χ ℓ k r' r1 N (fun _=>1) (fun _=>le_rfl) n z hβ
  have atKey (z:Fan.Stars H (leaves M)) (hT:Height.tiredN H ℓ z.1) :
      Poly.price w (matrix H M z)*Captain.wife N z.1 (leaves M) z.2 n ≤ b^Fintype.card V*(g^ℓ)⁻¹*S' z := by
    by_cases hZ:phase H M w z=0
    · rw [physical H M w hw,hZ,smul_zero,Poly.zero_price,zero_mul]
      exact mul_nonneg (mul_nonneg (pow_nonneg bp.le _) (inv_nonneg.mpr gp.le)) (major z)
    have occ:=occupied H M z (fun v=>(M v.2.val).charge/(Menu.sumFee (M v.2.val) w:ℂ)) hZ
    let p:=Captain.pearl z.1 (leaves M) r z.2
    let h:=Captain.wife N z.1 (leaves M) z.2 n
    have hp:0≤p:=Fan.pearlsNN (leaves M) H r r0 z
    have hphase:Poly.price w (matrix H M z)≤p:=by
      rw [physical H M w hw,Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
      exact (mul_le_mul_of_nonneg_left (unit H M w hw z) hp).trans (le_of_eq (mul_one _))
    have ze:=Fan.belayed (leaves M) H χ ℓ k r' N (fun _=>1) (fun _=>le_rfl) hβ n
      (fun _=>1) r' (fun _=>le_rfl) (fun _=>one_mul _ |>.symm) r1 z |>.2.1
    have ex:=exceptional H ℓ hβ hc ht z.1 hT
    have cz:Captain.pearl z.1 (leaves M) r' z.2=(b⁻¹)^Fintype.card (Occ H M z)*p:=by
      rw [←eβ];exact pearl_scale H M r _ z
    have scaled:g^ℓ*((b⁻¹)^Fintype.card (Occ H M z)*p*h)≤S' z:=by
      rw [←cz]
      exact (mul_le_mul_of_nonneg_right ex (mul_nonneg (Fan.pearlsNN (leaves M) H r' r1 z) (raw z))).trans ze
    have aa:0≤b^Fintype.card (Occ H M z)*(g^ℓ)⁻¹:=mul_nonneg (pow_nonneg bp.le _) (inv_nonneg.mpr gp.le)
    calc
      _ ≤ p*h:=mul_le_mul_of_nonneg_right hphase (raw z)
      _ = (b^Fintype.card (Occ H M z)*(g^ℓ)⁻¹)*(g^ℓ*((b⁻¹)^Fintype.card (Occ H M z)*p*h)):=by
        rw [inv_pow];field_simp [gp.ne',ne_of_gt bp]
      _ ≤ (b^Fintype.card (Occ H M z)*(g^ℓ)⁻¹)*S' z:=mul_le_mul_of_nonneg_left scaled aa
      _ ≤ _:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb occ) (inv_nonneg.mpr gp.le)) (major z)
  intro site
  apply budget_mono ((Quotes.hit_scale (mul_nonneg (pow_nonneg bp.le _) (inv_nonneg.mpr gp.le)) paid) site)
  · intro z
    dsimp only
    split_ifs <;> first | exact le_rfl | exact mul_nonneg (mul_nonneg (Poly.nonnegative hw _) (raw z)) (Real.exp_pos _).le | simp
  · intro z
    by_cases hz:site∈Captain.reachability z.1
    · simp only [if_pos hz]
      by_cases hT:Height.tiredN H ℓ z.1
      · rw [if_pos hT];exact mul_le_mul_of_nonneg_right (atKey z hT) (Real.exp_pos _).le
      · rw [if_neg hT,zero_mul]
        exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg bp.le _) (inv_nonneg.mpr gp.le)) (major z)) (Real.exp_pos _).le
    · simp only [if_neg hz,le_refl]

end Material

def horizon (p v:ℕ):=8*v+4*(p+1)

theorem billed (β:ℝ) (hβ:1≤β) (p v:ℕ) :
    (β^2)^v*((β^(3/8:ℝ))^horizon p v)⁻¹≤β^(-((p:ℝ)+1)/2) := by
  have hp:0<β:=zero_lt_one.trans_le hβ
  rw [←Real.rpow_natCast (x:=β) (n:=2),←Real.rpow_natCast,←Real.rpow_mul hp.le,
    ←Real.rpow_natCast (x:=β^(3/8:ℝ)),←Real.rpow_mul hp.le,←Real.rpow_neg hp.le,←Real.rpow_add hp]
  apply Real.rpow_le_rpow_of_exponent_le hβ
  unfold horizon
  push_cast
  linarith

end YM.Integration.ManuscriptQLocalMarkedHeightTail

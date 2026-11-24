import YM.Integration.WilsonThermometerWeakGroupAperture

/-! Read the actual masked exponential entry of a displaced Wilson arm on its local
healthy chart. The true exterior, far occurrences and physical coupling are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakGroupCoupon
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open Perch Glimmer LiftMark Beamer Atlas Tariffs MvPolynomial Ribbon Asymptotics
open WilsonThermometerWeakTaylor WilsonThermometerWeakPrimary WilsonThermometerWeakGroupAperture
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {C:Family G} {d D k N p b m:ℕ}
local notation "𝔽" => C.labels.level d
local notation "ℙ" => C.path.rep N p k

private theorem signs (x:C.label d) (U:Config G (C.side k p))
    (zero:Healthy (ℙ).p.threshold {0} U) :
    (∑' j:LA C d,weights C (ℙ).p.threshold x j*
      masked (ℙ).p.threshold (verseX C d k p j) (verseA C d k p j) U)=
      x 0+masked (ℙ).p.threshold ((C.localSection d).footprint 0)
          ((C.localSection d).places ((𝔽).scaled (ℙ).p.threshold⁻¹ ((𝔽).core x)) 0) U := by
  let z:=(𝔽).scaled (ℙ).p.threshold⁻¹ ((𝔽).core x)
  have hz:z=∑ i,z i • Pi.single i 1 := by ext1 i;simp [Pi.single_apply]
  have he:(∑ i,z i*((C.localSection d).places (Pi.single i 1) 0 U))=
      (C.localSection d).places z 0 U := by
    conv_rhs => rw [hz]
    unfold SectionData.places SectionData.evaluate
    rw [map_sum,map_sum];simp_rw [map_smul];rfl
  rw [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_unique]
  change x 0*masked (ℙ).p.threshold {0} (fun _=>1) U+
    (∑ i,z i*masked (ℙ).p.threshold ((C.localSection d).footprint 0)
       ((C.localSection d).places (Pi.single i 1) 0) U)=_
  rw [masked_eq _ _ _ _ zero,mul_one]
  by_cases ok:Healthy (ℙ).p.threshold ((C.localSection d).footprint 0) U
  · simp only [masked_eq _ _ _ _ ok];exact congrArg (x 0+·) he
  · simp only [masked_ne _ _ _ _ ok,mul_zero,Finset.sum_const_zero,add_zero]

theorem original (S:Rules G) (K:Provision C d k N p m b) (X:Coefficient 𝔽 (C.side k p))
    (form:X.Format 0 C.params ℙ) {q u v:poly (Up C k p b)} {a e cap cash:ℝ}
    (hq:Summary S (ℙ).p b D (verseX C d k p) (verseA C d k p)
      (weights C (ℙ).p.threshold X.x) a cap q)
    (hu:Summary S (ℙ).p b D (fun j:Near (P:=ℙ) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) e cash u)
    (hv:Summary S (ℙ).p b D (fun j:Far (P:=ℙ) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) e (expCut (ℙ).p m*cash) v)
    {g t:ℝ} (hg:0<g) (ht:0<t) (ht':t≤(ℙ).p.threshold) (U:Config G (C.side k p))
    (good:Healthy t (Spindle.patch b 0) U) (small:4*b*t≤S.c) :
    let r:=2*(4*b*t)/(ℙ).p.threshold
    let w:=(S.C+G.colorScale)*(4*b*t)^2/(ℙ).p.threshold
    r≤pane S → w+r≤1 →
    ‖X.exponentialEntry 0 (C.localSection d) ℙ U-
      signet 0 g (sender K.length (ℙ).p.threshold g (q+(u+v))) U‖ ≤
      (cap+cash+expCut (ℙ).p m*cash)*r^(D+1)+2*(expCut (ℙ).p m*cash)+
        coin (q+(u+v))*(D*w) := by
  intro r w hr hw
  let x:=wired (ℙ).p.threshold 0 b U
  let y:=rows (o:=(0:Site (C.side k p))) (ℙ).p.threshold K.length (G.curvature ∘ registered b U 0)
  let W:=q+(u+v)
  let L (j:LA C d):= weights C (ℙ).p.threshold X.x j*
      masked (ℙ).p.threshold (verseX C d k p j) (verseA C d k p j) U
  let Z (j:ℕ):=X.maskedTerm ℙ j U
  have zi:({0}:Support (C.side k p))⊆Spindle.patch b 0 := by
    intro j hj;rw [show j=0 from Finset.mem_singleton.mp hj,doors,separation_self];exact Nat.zero_le _
  have ff:flags (ℙ).p.threshold U⊆flags t U := by
    intro j hj;obtain ⟨face,inc,lt⟩:=(flags_spec _ _ _).mp hj
    exact (flags_spec _ _ _).mpr ⟨face,inc,ht'.trans_lt lt⟩
  have inside (j:LA C d):verseX C d k p j⊆Spindle.patch b 0 := by
    cases j with
    | inl _ => exact zi
    | inr _ => rw [patch_eq]; exact Finset.image_subset_image K.footprint
  have around (j:Near (P:=ℙ) X m):X.support j⊆Spindle.patch b 0 := by
    intro i hi;rw [doors]
    exact (Corona.extent _ (ℙ).p.B (form.origin _) hi).trans
      ((Nat.add_le_add_right (Nat.mul_le_mul_right _ j.property) _).trans K.cuts)
  have first: ‖(∑' j,L j)-text (scan x) q‖≤cap*r^(D+1) :=
    localWord hq inside K.length U ht ht' good small hr
  have second: ‖(∑' j:Near (P:=ℙ) X m,Z j)-text (scan x) u‖≤cash*r^(D+1) := by
    simpa only [one_mul,Z,Coefficient.maskedTerm,x,r] using localWord hu around K.length U ht ht' good small hr
  obtain ⟨ha,-,hi⟩:=closer S K.length U good (ℙ).p.threshold (ℙ).p.threshold_pos ht small
  have xc:‖x‖≤pane S:=ha.trans hr
  have fc:0≤expCut (ℙ).p m*cash := ((deposit hv U).2.trans' (norm_nonneg _))
  have third:‖(∑' j:Far (P:=ℙ) X m,Z j)-text (scan x) v‖≤expCut (ℙ).p m*cash*(2+r^(D+1)) := by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left (add_le_add (le_refl (2:ℝ)) (pow_le_pow_left₀ (norm_nonneg _) ha (D+1))) fc)
    simpa only [one_mul,Z,Coefficient.maskedTerm] using farWord hv U x xc
  have nearSum:Summable (fun j:Near (P:=ℙ) X m=>Z j) := by
    simpa only [one_mul,Z,Coefficient.maskedTerm] using (deposit hu U).1.of_norm
  have farSum:Summable (fun j:Far (P:=ℙ) X m=>Z j) := by
    simpa only [one_mul,Z,Coefficient.maskedTerm] using (deposit hv U).1.of_norm
  let M:Set ℕ:=setOf fun i => coverNumber (ℙ).p.B (X.support i) ≤ m
  have exhaust:((∑' j:Near (P:=ℙ) X m,Z j)+∑' j:Far (P:=ℙ) X m,Z j)=∑' j,Z j :=
    Summable.tsum_add_tsum_compl (s:=M) (f:=Z) nearSum farSum
  have entry:X.exponentialEntry 0 (C.localSection d) ℙ U=
      (∑' j,L j)+((∑' j:Near (P:=ℙ) X m,Z j)+∑' j:Far (P:=ℙ) X m,Z j) := by
    rw [exhaust,show (∑' j,L j)=_ from signs X.x U ((good.mono_left zi).mono_right ff)]
    rfl
  have diff:‖X.exponentialEntry 0 (C.localSection d) ℙ U-text (scan x) W‖≤
      (cap+cash+expCut (ℙ).p m*cash)*r^(D+1)+2*(expCut (ℙ).p m*cash) := by
    rw [entry];dsimp only [W];simp only [map_add]
    rw [show (∑' j,L j)+((∑' j:Near (P:=ℙ) X m,Z j)+∑' j:Far (P:=ℙ) X m,Z j)-
      (text (scan x) q+(text (scan x) u+text (scan x) v))=
      ((∑' j,L j)-text (scan x) q)+(((∑' j:Near (P:=ℙ) X m,Z j)-text (scan x) u)+
      ((∑' j:Far (P:=ℙ) X m,Z j)-text (scan x) v)) by abel]
    exact (norm_add_le ..).trans ((add_le_add first ((norm_add_le ..).trans (add_le_add second third))).trans_eq (by ring))
  have yc:‖y‖≤1:=le_trans (show ‖y‖≤‖y-x‖+‖x‖ from (le_of_eq (congrArg norm (sub_add_cancel y x).symm)).trans (norm_add_le ..))
      ((add_le_add ((norm_sub_rev ..).trans_le hi) ha).trans hw)
  have deg (T:poly (Up C k p b)) {ι:Type} {X':ι→Support (C.side k p)}
      {A':ι → Config G (C.side k p) → ℂ} {f':ι→ℂ} {h z:ℝ}
      (Y:Summary S (ℙ).p b D X' A' f' h z T) : T.totalDegree≤D :=
    Y.choose_spec.2.produced.choose_spec.1.degree
  have total:W.totalDegree≤D := (totalDegree_add ..).trans
    (max_le (deg _ hq) ((totalDegree_add ..).trans (max_le (deg _ hu) (deg _ hv))))
  rw [lets K.length _ hg]
  change ‖X.exponentialEntry 0 (C.localSection d) ℙ U-text (scan y) W‖≤_
  rw [show X.exponentialEntry 0 (C.localSection d) ℙ U-text (scan y) W=
    (X.exponentialEntry 0 (C.localSection d) ℙ U-text (scan x) W)+(text (scan x) W-text (scan y) W) by abel]
  exact (norm_add_le ..).trans (add_le_add diff ((moving W D total x y
    (xc.trans ((pane_le S).trans (by norm_num))) yc).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg D)) (sign _ _ zero_le_one))))

end YM.Integration.WilsonThermometerWeakGroupCoupon
end

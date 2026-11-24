import YM.FormalBulk08.Flat.Pole

/-!
# Quantitative real nonprincipal history sums

At the shared base momentum compare aliases using their centered lifts.
New aliases are in a genuine high tail, irrespective of the next L. On shared
aliases use displacement estimates also at growing momenta; `alias_perturb`
uses BOTH powers of the inverse denominator's alias gain. No constants after
a total depth choice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Precision RG Next.Free UVExtension.Free
open scoped Topology BigOperators
variable {G : Gauge}

def BlowCap (b : ℝ) := ∀ (L : Side), Odd L.val → ∀ l : Site L, l≠0 →
    ∀ p ∈ baseCube, b*grade l^2 ≤ ‖blow 1 p l‖

lemma blow_priced : ∃ b : ℝ, 0 < b ∧ BlowCap b := by
  classical
  let I := Σ t : {L : Side // Odd L.val}, {l : Site t.val // l ≠ 0}
  obtain ⟨σ,C,hσ,hC,h⟩ := blow_firm (fun x : I=>x.1.val) (fun _=>1) (fun x=>x.1.property) (fun x=>x.2.val) (fun x=>x.2.property)
  exact ⟨C,hC,fun L hL l hl p hp=> h ⟨⟨L,hL⟩,l,hl⟩ _ (base_subset_realCube hσ hp)⟩

def lifted (p : Momentum) (l : Cover) := p+reciprocal l
lemma alias_centre (p : Momentum) (L : Side) (l : Site L) : aliasAt p l=narrow L (lifted p (lift l)) := by ext j; rw [alias_value,narrow_apply]; rfl
lemma alias_physical (p : Momentum) (l : Cover) (hp : physical p) : physical (lifted p l) := by
  unfold lifted physical; rw [star_add, show star p=p from hp]; congr 1; funext i; simp [reciprocal]
lemma alias_pole (p : Momentum) (L : Side) (l : Site L) : blow 1 p l=divisor L (lifted p (lift l)) := by
  rw [← (show blow 1 (lifted p (lift l)) (0 : Site L)=_ from ((blow_zero ..).trans (congr_arg (fun L => divisor L _) (mul_one L))))]
  unfold blow; rw [alias_zero_eq,alias_centre]
lemma alias_price (p : Momentum) (hp : p ∈ baseCube) (L : Side) (l : Site L) :
    ‖lifted p (lift l)‖ ≤ (2*Real.pi)*grade l := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (grade_pos _).le)).mpr
  intro a
  have he := scaled_alias_upper l (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) a
  rw [alias_centre,narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos L).ne'] at he
  exact he.trans (mul_le_mul_of_nonneg_left (up_le ..) (by positivity))
lemma grade_agrees {L M : Side} (l : Site L) (r : Site M) (hx : lift l=lift r) : grade l=grade r := by unfold grade pdist; rw [hx]
lemma decay_agrees (i : ℕ) {L M : Side} (l : Site L) (r : Site M) (hx : lift l=lift r) : decay i l=decay i r := by unfold decay mix up; rw [hx]

def bump (b : ℝ) := 32*(2*Real.pi)^3/(b*b)

lemma alias_perturb {b : ℝ} (hb : 0<b) (h : BlowCap b) (p : Momentum) (hp : p ∈ baseCube)
    (L M : Side) (hL : Odd L.val) (hM : Odd M.val) (l : Site L) (r : Site M) (hl : l≠0) (hr : r≠0) (hm : L.val≤M.val) (hx : lift l=lift r) :
    ‖(blow 1 p l)⁻¹-(blow 1 p r)⁻¹‖ ≤ bump b/L.val := by
  let q := lifted p (lift l)
  have ht : ‖blow 1 p l-blow 1 p r‖ ≤ 32*((2*Real.pi)*grade l)^3/L.val := by
    rw [alias_pole,alias_pole,← hx]
    apply (divisor_difference L M hm q (alias_physical p _ hp.1)).trans
    gcongr; exact alias_price p hp _ _
  have hy := inv_move (mul_pos hb (pow_pos (grade_pos l) _)) (mul_pos hb (pow_pos (grade_pos r) _))
    (h L hL l hl p hp) (h M hM r hr p hp) ht
  rw [← grade_agrees l r hx] at hy
  apply hy.trans
  have hG := grade_ge l; have hW := grade_pos l; have hv : 0 ≤ bump b / L.val := by unfold bump; positivity
  calc
    _ = (bump b/L.val) / grade l := by unfold bump; field_simp
    _ ≤ _ := div_le_self hv hG

def DriveCap (i : ℕ) (B : ℝ) := ∀ (V : Train i) (p : Momentum), p∈baseCube →
    ∀ l : Site V.mass, ∀ a : Axis, ‖V.drive a (aliasAt p l)‖ ≤ B*decay i l
lemma drive_cap (i : ℕ) : ∃ B, 0 < B ∧ DriveCap i B := by
  obtain ⟨C,hC,h⟩ := Train.smooth_upper i
  refine ⟨C,hC,fun V p hp l a => ?_⟩
  let z := aliasAt p l a
  have he : z.im=0 := (physical_iff _).1 (alias_real hp.1 _) a
  unfold Train.drive; rw [norm_mul]
  apply (mul_le_of_le_one_right (norm_nonneg _) ((rail_height V.mass z).trans_eq ?_)).trans
    (h V p (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) l)
  simp [he]

lemma yen_equal {j : ℕ} (V : Train j) (p : Momentum) (hp : physical p) (a) :
    yen (V.drive a) p=V.drive a p*star (V.drive a p) := by rw [Train.drive_flip, show star p=p from hp]; rfl

private def raw (j : ℕ) (B b : ℝ) := B^2*bump b+(B*2)*(3*driveCost j)*(2*Real.pi)*b⁻¹
private lemma raw_cost (A : Levels G) (p : Momentum) (hp : p ∈ baseCube) (i a d D) (B b : ℝ) (hb : 0<b)
    (ht : BlowCap b) (hB : 0<B) (h : DriveCap (A.clock.J i) B) (he : d≤D)
    (l : Site (flying A d i).mass) (r : Site (flying A D i).mass) (hl : l≠0) (hr : r≠0)
    (hx : lift l=lift r) :
    let V := flying A d i; let W := flying A D i
    let q:=aliasAt p l; let w:=aliasAt p r
    ‖yen (V.drive a) q * (blow 1 p l)⁻¹ - yen (W.drive a) w * (blow 1 p r)⁻¹‖ ≤
      raw (A.clock.J i) B b * (Real.sqrt V.mass.val)⁻¹ * decay 2 l := by
  intro V W q w
  let M:=V.mass; let N:=W.mass; let j:=A.clock.J i
  let I := Real.sqrt (M.val:ℝ); have hI : 0<I := Real.sqrt_pos.mpr (side_pos M)
  have hJ : 3 ≤ j := (by decide : 3 ≤ 4).trans (A.clock.adm _)
  have hm : M.val ≤ N.val := by unfold M N V W; rw [flying_mass,flying_mass]; exact steps_incr _ _ _ he _
  have hg : B*decay j l ≤ B*decay 3 l := mul_le_mul_of_nonneg_left (decay_anti l hJ) hB.le
  have h₁ := (h V p hp l a).trans hg
  rw [decay_agrees j l r hx, decay_agrees 3 l r hx] at hg
  have h₂ := (h W p hp r a).trans hg
  rw [← decay_agrees 3 l r hx] at h₂
  let Q := lifted p (lift l)
  let k := 3*driveCost j*(2*Real.pi)
  have hd : ‖V.drive a q-W.drive a w‖ ≤ k*grade l*I⁻¹ := by
    unfold q w; rw [alias_centre,alias_centre,← hx]
    have hc := drive_rate A a i d D Q (alias_physical _ _ hp.1) he; rw [← flying_mass A, ← flying_mass A] at hc
    refine hc.trans ?_; change 3*driveCost j*‖Q‖*I⁻¹ ≤ _
    have hh := driveCost_pos j
    unfold k; rw [mul_assoc _ (2*Real.pi)]; gcongr; exact alias_price p hp _ _
  have hs : ‖yen (V.drive a) q-yen (W.drive a) w‖ ≤ B*2*k*I⁻¹*decay 2 l := by
    rw [yen_equal _ _ (alias_real hp.1 _),yen_equal _ _ (alias_real hp.1 _)]
    have hK := product_move _ _ _ _ hd (show ‖star (V.drive a q)-star (W.drive a w)‖≤k*grade l*I⁻¹ by rw [← star_sub,norm_star]; exact hd)
      h₁ (show ‖star (W.drive a w)‖≤B*decay 3 l by rw [norm_star]; exact h₂)
    apply hK.trans
    have hr : grade l * decay 3 l ≤ decay 2 l := by simpa only [pow_one] using absorbs l 1 2
    calc
      _ = (B*2*k*I⁻¹)*(grade l*decay 3 l) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by unfold k; have hx := driveCost_pos j; positivity)
  have hR : ‖(blow 1 p r)⁻¹‖ ≤ b⁻¹ := by
    have hv := (le_mul_of_one_le_right hb.le (one_le_pow₀ (grade_ge r))).trans (ht _ W.mass_odd r hr p hp)
    rw [norm_inv]; exact inv_le_inv₀ (hb.trans_le hv) hb|>.2 hv
  have hS := product_move _ _ _ _ hs (alias_perturb hb ht p hp M N V.mass_odd W.mass_odd l r hl hr hm hx) (show ‖yen (V.drive a) q‖≤B^2*decay 2 l from ?_) hR
  · apply hS.trans
    have hk : 0≤bump b := by unfold bump; positivity
    have hS : bump b / (M.val:ℝ) ≤ bump b * I⁻¹ := by rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left hk hI (sqrt_mass M).2
    refine (add_le_add_left (mul_le_mul_of_nonneg_left hS (mul_nonneg (sq_nonneg _) (decay_pos _ _).le)) _).trans_eq ?_
    change _=raw j B b*I⁻¹*_; unfold raw k; ring
  rw [yen_equal _ _ (alias_real hp.1 _),norm_mul,norm_star,← pow_two]
  apply (pow_le_pow_left₀ (norm_nonneg _) h₁ _).trans; rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _); rw [pow_two]
  exact (mul_le_of_le_one_right (decay_pos ..).le (decay_le_one ..)).trans (decay_anti _ (by decide : 2≤3))

lemma lift_keep {L M : Side} (hm : L.val ≤ M.val) (l : Site L) : lift (wrap M (lift l))=lift l := by
  refine lift_eq_iff.mpr ⟨rfl,fun j=>?_⟩
  obtain ⟨hv,hw⟩:= lift_centers l j; omega

lemma spend_absent (L M : Side) (r : Site M) (hr : lift (wrap L (lift r))≠lift r) :
    (L.val:ℝ) ≤ 2*grade r := by
  have hh : ¬∀ i, (-(L.val:ℤ)<2*lift r i ∧ 2*lift r i ≤ L.val) := fun he=> hr (lift_eq_iff.mpr ⟨rfl,he⟩)
  push Not at hh
  obtain ⟨i,hi⟩ := hh
  have hx : L.val ≤ 2*(lift r i).natAbs := by omega
  have hv := up_le r i
  have ht : (L.val:ℝ) ≤ 2*((lift r i).natAbs:ℝ) := by exact_mod_cast hx
  unfold up at hv; linarith

private lemma raw_missing (L : Side) (A : Levels G) (p : Momentum) (hp : p ∈ baseCube) (i a d)
    (B b : ℝ) (hb : 0<b) (ht : BlowCap b) (hB : 0<B) (h : DriveCap (A.clock.J i) B)
    (r : Site (flying A d i).mass) (hr : r≠0) (hx : lift (wrap L (lift r))≠lift r) :
    let V := flying A d i; let q:=aliasAt p r
    ‖yen (V.drive a) q * (blow 1 p r)⁻¹‖ ≤
      (2*B^2*b⁻¹ * (Real.sqrt (L.val:ℝ))⁻¹) * decay 2 r := by
  intro V q
  rw [yen_equal _ _ (alias_real hp.1 _), norm_mul,norm_mul,norm_star]
  have hi : 3 ≤ A.clock.J i := (by decide : 3 ≤ 4).trans (A.clock.adm _)
  have hg := ht V.mass V.mass_odd r hr p hp
  have hR : ‖(blow 1 p r)⁻¹‖ ≤ b⁻¹ := by
    have hv := (le_mul_of_one_le_right hb.le (one_le_pow₀ (grade_ge r))).trans hg
    rw [norm_inv]; exact inv_le_inv₀ (hb.trans_le hv) hb|>.2 hv
  let I:=Real.sqrt (L.val:ℝ); have hI : 0<I:= Real.sqrt_pos.mpr (side_pos L)
  have he : ‖V.drive a q‖ ≤ B*decay 3 r :=
    (h V p hp r a).trans (mul_le_mul_of_nonneg_left (decay_anti _ hi) hB.le)
  have hy : ‖V.drive a q‖ ≤ B := he.trans (mul_le_of_le_one_right hB.le (decay_le_one ..))
  have hh : I ≤ 2*grade r := (sqrt_mass L).2.trans (spend_absent L V.mass r hx)
  have hw : decay 3 r ≤ 2*decay 2 r/I := by
    apply (le_div_iff₀ hI).mpr
    have hm := mul_le_mul_of_nonneg_right hh (decay_pos r 3).le
    have hv : grade r * decay 3 r ≤ decay 2 r := by simpa only [pow_one] using absorbs r 1 2
    linarith only [hm,hv]
  calc
    _ ≤ (B*(2*decay 2 r/I))*B*b⁻¹ := mul_le_mul (mul_le_mul (he.trans (mul_le_mul_of_nonneg_left hw hB.le)) hy (norm_nonneg _) ((norm_nonneg _).trans (he.trans (mul_le_mul_of_nonneg_left hw hB.le)))) hR (norm_nonneg _) (by have hx:= decay_pos r 2; positivity)
    _ = _ := by unfold I; ring

/-- The exponent is numerical and the constant is set before the path and
blocks. -/
theorem high_rate (j : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ (A : Levels G) (i d D : ℕ) (p : Momentum)
    (a : Axis), A.clock.J i=j → p∈baseCube → d≤D →
    ‖(flying A d i).high a p-(flying A D i).high a p‖ ≤ C*(Real.sqrt (A.S.steps i d).val)⁻¹ := by
  obtain ⟨B,hB,h⟩:=drive_cap j
  obtain ⟨b,hb,ht⟩:=blow_priced
  obtain ⟨R,hR,H⟩:=decay_cost
  have hT : 0 < raw j B b := by unfold raw bump; have := driveCost_pos j; positivity
  refine ⟨(raw j B b+2*B^2*b⁻¹)*R,by positivity,fun A i d D p a ha hp hD=> ?_⟩
  subst j
  let j:=A.clock.J i
  let V:=flying A d i; let W:=flying A D i
  let M:=V.mass; let N:=W.mass
  let f := fun l : Site M => yen (V.drive a) (aliasAt p l) * (blow 1 p l)⁻¹
  let g := fun l : Site N => yen (W.drive a) (aliasAt p l) * (blow 1 p l)⁻¹
  let e := fun l : Site M => wrap N (lift l)
  let s := Finset.univ.erase (0 : Site M); let t := Finset.univ.erase (0 : Site N)
  let u := s.image e
  let I:=Real.sqrt (M.val:ℝ); have hI:0<I:= Real.sqrt_pos.mpr (side_pos M)
  have hm : M.val ≤ N.val := by unfold M N V W; rw [flying_mass,flying_mass]; exact steps_incr _ _ _ hD _
  have he l : lift (e l)=lift l := lift_keep hm l
  have hin : Injective e := fun i j hh=> lift_inj ( (he i).symm.trans ((congr_arg lift hh).trans (he j)))
  have hz (r : Site N) (hr : r∈ t\u) : lift (wrap M (lift r))≠lift r := by
    obtain ⟨hh,hk⟩ := Finset.mem_sdiff.mp hr
    have hb : r≠0 := (Finset.mem_erase.mp hh).1
    intro hp
    apply hk
    apply Finset.mem_image.mpr; refine ⟨_,Finset.mem_erase.mpr ⟨?_,Finset.mem_univ (wrap M (lift r))⟩, ?_⟩
    · intro hx
      rw [hx,lift_origin] at hp
      exact hb (lift_inj (hp.symm.trans (lift_origin N).symm))
    apply lift_inj; rw [he,hp]
  have hE : u ⊆ t := by
    rintro k hk
    obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp hk
    refine Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hl).1 ?_,Finset.mem_univ _⟩
    apply hin; simpa [e] using h
  rw [← flying_mass A]
  change ‖(∑ l∈s,f l)-(∑ l ∈ t,g l)‖ ≤ (raw j B b+ _)*R*I⁻¹
  have hk (l : Site M) (hl : l ∈ s) : ‖f l-g (e l)‖ ≤ raw j B b*I⁻¹*decay 2 l :=
    raw_cost A p hp i a d D B b hb ht hB h hD _ _ (Finset.mem_erase.mp hl).1
      (Finset.mem_erase.mp (hE (Finset.mem_image_of_mem _ hl))).1 (he _).symm
  have hl : ‖(∑ l∈s,f l)-∑ r∈u,g r‖ ≤ raw j B b*I⁻¹ * R := by
    unfold u; rw [Finset.sum_image hin.injOn, ← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans ((Finset.sum_le_sum hk).trans ?_)
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> (decay_pos ..).le)).trans (H _)) ?_
    exact mul_nonneg hT.le (inv_nonneg.mpr hI.le)
  have hf : ‖∑ r∈t\u, g r‖ ≤ 2*B^2*b⁻¹*I⁻¹ * R := by
    apply (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun l=> 2*B^2*b⁻¹*I⁻¹*decay 2 l)
      (fun l hl=>raw_missing M A p hp _ a D B b hb ht hB h l (Finset.mem_erase.mp (Finset.mem_sdiff.mp hl).1).1 (hz _ hl))).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> (decay_pos ..).le)).trans (H _)) (by positivity)
  rw [← Finset.sum_sdiff hE, add_comm (∑ r∈t\u,g r), ← sub_sub]
  exact (norm_sub_le ..).trans ((add_le_add hl hf).trans_eq (by ring))
end YM.FormalBulk08.Flat

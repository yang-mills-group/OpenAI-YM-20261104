import YM.FormalBulk08.Flat.Both

/-!
Accounting. The apparent inverse and pole powers in the REAL estimates
are disposable: they are used just once before strip interpolation. Uniform
over all levels and calendar data in the probes, subject to the displayed
scale/stage matches.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free
open scoped Topology BigOperators
variable {G : Gauge} {ι : Type*}

variable {j : ℕ}
/-- Literally a request on overlapping stages. -/
structure Probe (V W : ι→Train j) (A : ι→Levels G) (i N N' : ι→ℕ) where
  sizes x : i x≤N x
  lengths x : N x≤N' x
  which x : (A x).clock.J (i x)=j
  -- HEq used only to avoid casting towers
  from_V x : HEq (V x) (location (A x) (N x) (i x))
  from_W x : HEq (W x) (location (A x) (N' x) (i x))

structure Range (p : ι→Momentum) (w : ι→ℝ) : Prop where
  atLeast x : 1≤w x
  cube x : p x ∈ baseCube
  away x : p x ≠ 0
  radius : ∃ K : ℝ, 0<K ∧ ∀ x, ‖p x‖⁻¹ ≤ K*w x


namespace Range
variable {p : ι→Momentum} {w : ι→ℝ}
lemma normed (h : Range p w) x : 0<‖p x‖:=norm_pos_iff.mpr (h.away x)
lemma price (h : Range p w) x : ‖p x‖≤ domainRadius := box_price _ (h.cube x)
lemma fund (h : Range p w) x : 0<w x := one_pos.trans_le (h.atLeast _)
lemma restrict_weight (p : ι → Momentum) (hx : ∀ x,p x∈baseCube) (hp : ∀ x, p x ≠ 0) :
    Range p (fun i=>domainRadius/‖p i‖) := ⟨fun i=> (one_le_div (norm_pos_iff.mpr (hp i))).mpr (box_price _ (hx i)),hx,hp,domainRadius⁻¹,inv_pos.mpr domainRadius_pos,fun x=> le_of_eq (by field_simp [domainRadius_pos.ne'])⟩
lemma on_axis (h : Range p w) {r : ι→ℝ} (hr : ∀ x,0≤r x) (f : Momentum→ℂ) (hf : Continuous f) :
    Paired w r 0 (fun x=>f (p x)) (fun x=>f (p x)) := by
  apply Paired.equal hr
  have ht : IsCompact (Metric.closedBall (0: Momentum) domainRadius) := isCompact_closedBall ..
  obtain ⟨C,hC⟩ := (ht.image hf.norm).bddAbove
  exact ⟨C,fun i=> hC ⟨p i,(by simpa [Metric.mem_closedBall] using (h.price i)),rfl⟩⟩
lemma images (hx : Range p w) (L : Side) (ho : Odd L.val) (l : Site L) :
    Range (fun x=> aliasAt (p x) l) w := by
  have ht x := alias_base (hx.cube x) l ho
  by_cases h : l=0
  · subst l
    simp_rw [alias_zero_eq] at *
    have he x : ‖narrow L (p x)‖ = (L.val:ℝ)⁻¹ * ‖p x‖ := by rw [narrow,norm_smul,norm_inv,Complex.norm_natCast]
    obtain ⟨K,hK,h⟩ := hx.radius
    refine ⟨hx.atLeast,ht, fun x=> norm_pos_iff.mp ((mul_pos (inv_pos.mpr (side_pos L)) (hx.normed x)).trans_eq (he x).symm), K*L.val, by positivity, fun x=> ?_⟩
    rw [he,_root_.mul_inv_rev,inv_inv]; exact (mul_le_mul_of_nonneg_right (h x) (side_pos L).le).trans_eq (by ring)
  obtain ⟨a,ha⟩ := Function.ne_iff.mp (show lift l ≠ 0 by rw [← lift_origin L]; exact lift_inj.ne h)
  let C := zone*up l a/L.val
  have hp : 0<C := div_pos (mul_pos zone_pos (up_pos ..)) (side_pos _)
  have hw x : C ≤ ‖aliasAt (p x) l‖ := by
    have he := scaled_alias_lower l (mem_cube_real (base_subset_realCube zone_pos (hx.cube x)) zone_pos) a ha
    exact le_trans ((div_le_iff₀ (side_pos _)).mpr (he.trans_eq (mul_comm ..))) (norm_le_pi_norm _ _)
  refine ⟨hx.atLeast,ht,fun x=> norm_pos_iff.mp (hp.trans_le (hw x)), C⁻¹,inv_pos.mpr hp,fun x=>?_⟩
  exact ((inv_le_inv₀ (hp.trans_le (hw x)) hp).mpr (hw x)).trans (le_mul_of_one_le_right (inv_pos.mpr hp).le (hx.atLeast x))
end Range

def fineR (A : Levels G) (N i : ℕ) : ℝ := (Real.sqrt (A.S.steps i (N-i)).val)⁻¹
lemma fineR_pos (A : Levels G) (N i : ℕ) : 0 < fineR A N i := inv_pos.mpr (Real.sqrt_pos.mpr (side_pos _))

namespace Probe
variable {j : ℕ} {V W : ι → Train j} {A : ι→Levels G} {i N N' : ι→ℕ} {p : ι→Momentum} {w r : ι→ℝ}
variable (h : Probe V W A i N N') (hj : 4≤j) (hx : Range p w)
variable (hr : ∀ x, fineR (A x) (N x) (i x) ≤ r x) (k : ℝ) (hk : 0 < k)
include h hj hx hr hk

lemma basic (a : Axis) : Paired w r 2 (fun x=> (V x).levelD k a (p x)) (fun x=> (W x).levelD k a (p x)) := by
  obtain ⟨E,hE,H⟩:=levelD_rate (G:=G) _ hj _ hk
  obtain ⟨b,C,hb,hC⟩:= levelD_caps _ hj _ hk
  obtain ⟨K,hK,ht⟩:= hx.radius
  let B:=max E C; have hB:0<B:=lt_max_of_lt_left hE
  have hy (i l m M p a) (U : Levels G) (he : HEq l (location U m i)) (ht : HEq M (location U p i))
      (hv : U.clock.J i=j) (hp : i≤m) (hN : m ≤ p) (x : Momentum) (hh : x∈baseCube) (hz:x≠0) :
      ‖(l:Train j).levelD k a x-(M:Train j).levelD k a x‖ ≤ E*fineR U m i / ‖x‖^2 := by
    -- shrink to the native types locally. Section h and hx not used here.
    subst j
    rw [eq_of_heq he,eq_of_heq ht]; exact H U i m p x a rfl hh hz hp hN
  refine ⟨B*K^2,mul_pos hB (pow_pos hK _),fun x=>?_⟩
  have hrx : 0< r x:= (fineR_pos ..).trans_le (hr x)
  have he (C' : ℝ) (A' : ℝ) (ha' : 0<A') (hC' : C'≤ B*A') :
      C'/ ‖p x‖^2 ≤ B*K^2*w x^2*A' := calc
    _ ≤ B*A' * (‖p x‖⁻¹)^2 := (div_le_div_of_nonneg_right hC' (by positivity)).trans_eq (by rw [inv_pow,div_eq_mul_inv])
    _ ≤ B*A' * (K*w x)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (ht x) _) (mul_pos hB ha').le
    _ = _ := by ring
  refine ⟨(hC (V x) _ _ (hx.cube x) (hx.away x)).2.trans ?_,(hC (W x) _ _ (hx.cube x) (hx.away x)).2.trans ?_,?_⟩
  · simpa only [mul_one] using he C 1 one_pos (by rw [mul_one]; exact le_max_right ..)
  · simpa only [mul_one] using he C 1 one_pos (by rw [mul_one]; exact le_max_right ..)
  apply (hy (i x) _ _ _ _ a _ (h.from_V x) (h.from_W x) (h.which x) (h.sizes x) (h.lengths x) _ (hx.cube x) (hx.away x)).trans
  exact he _ (r x) hrx (mul_le_mul (le_max_left ..) (hr x) (fineR_pos ..).le hB.le)
lemma backwards (a : Axis) : Paired w r 2 (fun i=> (Train.levelD k (V i) a (p i))⁻¹) (fun i=> (Train.levelD k (W i) a (p i))⁻¹) := by
  have ht := basic h hj hx hr k hk a
  refine ht.recip (s:=0) hx.atLeast (fun x=> ((fineR_pos ..).trans_le (hr x)).le) ?_
  obtain ⟨b,C,hb,hC⟩:=levelD_caps _ hj _ hk
  exact ⟨b,hb,fun x=> by simp only [pow_zero,div_one]; exact ⟨(hC (V x) _ _ (hx.cube x) (hx.away x)).1,(hC (W x) _ _ (hx.cube x) (hx.away x)).1⟩⟩
lemma quota : Paired w r 2 (fun x=> (V x).rho k (p x)) fun x=> (W x).rho k (p x) := by
  let Q i (F : ι → Train j) := fun x=> jewel 1 (p x) i*(Train.levelD k (F x) i (p x))⁻¹
  simp only [Train.rho, div_eq_mul_inv]
  have hc x := (fineR_pos ..).le.trans (hr x)
  refine Paired.sum Finset.univ hx.atLeast hc (fun i=> Q i V) (fun i=>Q i W) fun a _=>?_
  have hb : Continuous (fun p=>jewel 1 p a) := by unfold jewel seedQ chip narrow; fun_prop
  exact (hx.on_axis hc _ hb).mul (backwards h hj hx hr k hk a)
lemma quota_back : Paired w r 10 (fun x=> ((V x).rho k (p x))⁻¹) fun x=> ((W x).rho k (p x))⁻¹ := by
  have hc x := (fineR_pos ..).le.trans (hr x)
  apply (quota h hj hx hr k hk).recip hx.atLeast hc (s:=4)
  obtain ⟨c,hc,h⟩ := rho_real_floor _ hj k hk
  obtain ⟨B,hB,H⟩ := hx.radius
  refine ⟨c/B^4,by positivity,fun x=>?_⟩
  have hp := hx.normed x
  have hv : c/B^4/w x^4 ≤ c*‖p x‖^4 := by
    have hB := mul_pos hB (hx.fund x)
    have he : (B*w x)⁻¹ ≤ ‖p x‖ := ((inv_le_inv₀ hB (inv_pos.mpr hp)).mpr (H x)).trans_eq (inv_inv _)
    calc
      _ = c*((B*w x)⁻¹)^4 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hB).le he _) hc.le
  exact ⟨hv.trans (h (V x) _ (hx.cube x) (hx.away x)),hv.trans (h (W x) _ (hx.cube x) (hx.away x))⟩
lemma pink_tabs : Boards w r 14 (fun x => pulse k (V x) (p x)) fun x=> pulse k (W x) (p x) := by
  have H x := (backwards h hj hx hr k hk x)
  have hrN x := ((fineR_pos ..).le.trans (hr x))
  -- retain initial hr
  refine Boards.plugs (Boards.sm (quota_back h hj hx hr k hk)
    (Boards.mask_paired (fun x i=> (Train.levelD k (V x) i (p x))⁻¹) (fun x i=> (Train.levelD k (W x) i (p x))⁻¹) (n:=2) hx.atLeast hrN H)) ?_ ?_
  · intro x; exact (pulse_sources k hk (V x) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x)).symm
  intro x; exact (pulse_sources k hk (W x) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x)).symm
lemma blue_tabs : Boards w r 6 (fun x => vault k (V x) (p x)) fun x=> vault k (W x) (p x) := by
  have hr' x := ((fineR_pos ..).le.trans (hr x))
  refine Boards.plugs (Boards.sm (quota h hj hx hr k hk)
    (Boards.mask_paired (fun x i=> Train.levelD k (V x) i (p x)) (fun x i=> Train.levelD k (W x) i (p x)) (n:=2) hx.atLeast hr' (basic h hj hx hr k hk))) ?_ ?_
  · intro x; exact (vault_sources k hk (V x) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x)).symm
  intro x; exact (vault_sources k hk (W x) (base_subset_realCube zone_pos (hx.cube x)) (hx.away x)).symm
end Probe
end YM.FormalBulk08.Flat

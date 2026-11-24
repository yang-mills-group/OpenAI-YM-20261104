import YM.MSbar.Pole.Scale.Genuine

/-! # Laurent coefficient calculation in generic tensors -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I] {F G : ℂ → Cloud I} {k l : ℕ}

/-- `purePolar` represents the purely polar local insertions, ignoring values at zero.
Convention indexed by `i` ascending from 0 power −1; regardless of requested horizon. -/
def purePolar (k : ℕ) (f : ℕ→Cloud I) : ℂ→Cloud I := ∑ i∈Finset.range k,(fun z=> z⁻¹^(i+1) • f i)
@[simp] lemma purePolar_zero (f : ℕ→Cloud I) : purePolar 0 f=0 := by simp [purePolar]
lemma purePolar_up (k : ℕ) (f:ℕ→Cloud I) : purePolar (k+1) f=purePolar k f+ fun z=>z⁻¹^(k+1) • f k:= Finset.sum_range_succ ..

def Canonical (F : Cloud I) := Tensor F ∧ ∀ n, Packet (Set.univ:Set (External I n)) (ticket (@id _)) 1 (F n)
lemma Meridian.base {R:ℝ} (h : Meridian (zone R) F) (hr:0<R) : Canonical (F 0) :=
    ⟨h.tensor 0 (zone_zero hr), fun n=>(h.budget n).fixed (zone_zero hr)⟩
lemma Canonical.constant {G:Cloud I} (h : Canonical G) {U:Set ℂ} : Meridian U (fun _=>G):=⟨fun n=>Wall.freeze (h.2 n),fun _ _=> h.1⟩

lemma ext_cut (k : ℕ) (f g : ℕ→Cloud I) (h : ∀ i, i<k → f i = g i) : purePolar k f=purePolar k g := by
  induction k with
  | zero => simp
  | succ k ih => rw [purePolar_up,purePolar_up,ih (fun i hi=> h i (by omega)),h k (by omega)]
lemma remove (h : Vortex (k+1) F) : ∃ C : Cloud I, Canonical C ∧ Vortex k (F- fun z=>z⁻¹^(k+1) • C) := by
  obtain ⟨R,G,hr,H,h⟩:=h
  refine ⟨G 0,H.base hr,R,facets G,hr,facets_runs H hr, fun z hz n x=>?_⟩
  change z^k*(F z n x-z⁻¹^(k+1)*G 0 n x)= _
  have he : z≠0:=hz.2
  apply mul_left_cancel₀ he
  have hf := stress H hr n x z hz.1; rw [← h z hz] at hf
  calc
    _ = z^(k+1)*(F z n x-z⁻¹^(k+1)*G 0 n x) := by ring
    _ = z^(k+1)*F z n x-G 0 n x := by rw [mul_sub,← mul_assoc _ _ (G 0 n x), inv_pow, mul_inv_cancel₀ (pow_ne_zero _ he),one_mul]
    _ = z * facets G z n x := by rw [hf]; ring
lemma peel (h : Vortex k F) : ∃ C : ℕ→Cloud I, (∀ i,Canonical (C i)) ∧ Vortex 0 (F - purePolar k C) := by
  induction k generalizing F with
  | zero => refine ⟨0,fun _ => ⟨⟨fun _ _ _=> rfl,fun _ _=>rfl⟩,fun _=>Packet.zero⟩,?_⟩; simpa
  | succ k ih =>
    obtain ⟨C,H,hp⟩:=remove h
    obtain ⟨D,T,hq⟩:=ih hp
    let P := Function.update D k C
    refine ⟨P,fun i=>?_,?_⟩
    · by_cases hk:i=k
      · subst i; simp [P,H]
      simpa [P,hk] using T i
    rw [purePolar_up,ext_cut _ _ D (fun i hi=>update_of_ne hi.ne _ _),show P k=C from update_self .., add_comm,← sub_sub]; exact hq

lemma remainder {R:ℝ} (h : Meridian (zone R) F) (hr:0<R) {f : Cloud I}
    (h₀ : ∀ n x, Tendsto (fun z=>F z n x) (𝓝[≠] 0) (nhds (f n x))) : F 0=f:=funext fun n=>funext fun x=>
    tendsto_nhds_unique (((h.budget n).region 0 (zone_zero hr) x).continuousAt.continuousWithinAt) (h₀ _ _)

lemma pole_unique {C D:ℕ → Cloud I} (h : Vortex 0 (purePolar k C - purePolar k D)) : ∀ i, i<k→ C i = D i:= by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    have hv : C k=D k:= by
      obtain ⟨R,G,hr,H,h⟩:=h
      funext n x
      have hc (C : ℕ→ Cloud I) : Tendsto (fun z=> z^(k+1)*purePolar (k+1) C z n x) (𝓝[≠] 0) (nhds (C k n x)):= by
        let A (z : ℂ) := (∑ i∈Finset.range k,z^(k-i)*C i n x)+C k n x
        have he : A 0=C k n x:= by unfold A; rw [Finset.sum_eq_zero]; simp; intro i hi; have hh : i<k:= Finset.mem_range.mp hi; simp [show k-i≠0 by omega]
        have hs : Continuous A := (continuous_finsetSum _ (fun _ _=> (continuous_id.pow _).mul_const _)).add continuous_const
        rw [← he]; apply (hs.continuousAt.continuousWithinAt (x:=0) (s:={0}ᶜ)).congr' -- maybe order
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hv:z≠0:=hz
        rw [purePolar_up]
        change A z=z^(k+1)*(purePolar k C z n x + z⁻¹^(k+1)*C k n x)
        unfold A purePolar; simp only [Finset.sum_apply,mul_add,Pi.smul_apply, smul_eq_mul]
        congr 1
        · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=> ?_
          have ht : i<k:=Finset.mem_range.mp hi
          rw [← mul_assoc _ _ (C i n x),inv_pow, show k+1=k-i+(i+1) by omega,pow_add,mul_assoc _ _ ((z^(i+1))⁻¹), mul_inv_cancel₀ (pow_ne_zero _ hv),mul_one]
        rw [← mul_assoc _ _ (C k n x),inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hv),one_mul]
      apply sub_eq_zero.mp
      have hb := ((tendsto_id (x:=nhds (0:ℂ))).pow (k+1)).mul (((H.budget n).region 0 (zone_zero hr) x).continuousAt.tendsto)
      have hB : Tendsto (fun z : ℂ=> z^(k+1)*G z n x) (𝓝[≠] 0) (nhds 0):= by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        simpa using hb
      refine tendsto_nhds_unique_of_eventuallyEq ((hc C).sub (hc D)) hB ?_
      filter_upwards [neighborhood hr] with z hz
      change z^_ *_-z^_*_= z^_*_; rw [← mul_sub,← h _ hz]
      simp
    intro i hi; rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hh|hh
    · rw [purePolar_up,purePolar_up,hv, add_sub_add_right_eq_sub] at h; exact ih h i hh
    rw [hh]; exact hv
end YM.MSbar.Pole

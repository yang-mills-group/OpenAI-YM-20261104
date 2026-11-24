import YM.Integration.WilsonCenteredNestedOrigin

/-! A single spatial threshold for every linear combination of the actual
raw/public detector inputs, with their literal finite coefficient mass. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedShadowBasis
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}
abbrev Slot (S : Table C.book) (d : I→ℕ) := (i:I)→Fin (Module.finrank ℂ (S.Field (d i)))

def axis (S : Table C.book) (d : I→ℕ) (t : Slot S d) : Labels S d :=
  fun i=>Module.finBasis ℂ (S.Field (d i)) (t i)

def coeff (v : Labels S d) (t : Slot S d) : ℂ :=
  ∏ i,(Module.finBasis ℂ (S.Field (d i))).repr (v i) (t i)

def mass (v : Labels S d) : ℝ := ∑ t : Slot S d,‖coeff v t‖

def older (P : Prescription F.sector.derivatives) (h : ℕ) (x : I→E4) (o : E4) :
    MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field h) :=
  ∑ j∈bands F.sector.derivatives h,(LinearMap.toSpanSingleton ℂ _ (P.loaded j h)).compMultilinearMap (checkRow P j x o)

def newer (h : ℕ) (x : I→E4) (o : E4) : MultilinearMap ℂ (fun i=>S.Field (d i)) (S.Field h) :=
  ∑ j : Fin (h+1),(F.sector.derivatives.rise (d:=j.val) (Nat.le_of_lt_succ j.isLt)).compMultilinearMap (Q.fresh j.val x o)

lemma chart (P : Prescription F.sector.derivatives) (h : ℕ) (x : I→E4) (o : E4) (v : Labels S d) :
    (older F P h x o (d:=d) - newer F Q h x o (d:=d)) v = shadowOld P h x o v - Q.packet h x v o := by
  unfold older newer shadowOld shadow packet
  simp only [_root_.sub_apply,_root_.sum_apply,LinearMap.compMultilinearMap_apply,check_eq P _ Q.continuum,
    LinearMap.toSpanSingleton_apply]

lemma expand {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : MultilinearMap ℂ (fun i=>S.Field (d i)) V) (v : Labels S d) :
    A v = ∑ t : Slot S d, coeff v t • A (axis S d t) := by
  let b (i : I) := Module.finBasis ℂ (S.Field (d i))
  have hv : v=fun i=>∑ j,(b i).repr (v i) j • b i j := funext fun i=>((b i).sum_repr _).symm
  conv_lhs => rw [hv]
  rw [MultilinearMap.map_sum]
  exact Finset.sum_congr rfl fun t _=>A.map_smul_univ (fun i=>(b i).repr (v i) (t i)) _

/-- The original sheet coefficients fund the whole rotating input ball by
multilinearity. The physical threshold precedes all its amplitudes. -/
theorem original {P : Prescription F.sector.derivatives} (hp : P.Coherent)
    (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u)
    (h : ℕ) (d : I→ℕ) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(k : ℕ)(B : ℝ),0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(x:I→E4)(o:E4),WithinRoom r M η x o →
      ∀v : Labels S d,‖shadowOld P h x o v - Q.packet h x v o‖ ≤
        mass v * (wage k B r * r^((h:ℝ)+1-weight d)) := by
  let fare (t : Slot S d) (k : ℕ) (B : ℝ) := ∀ᶠ r:ℝ in 𝓝[>]0,∀(x:I→E4)(o:E4),WithinRoom r M η x o →
    ‖shadowOld P h x o (axis S d t) - Q.packet h x (axis S d t) o‖ ≤ wage k B r * r^((h:ℝ)+1-weight d)
  have widen (t : Slot S d) (k : ℕ) (B : ℝ) (j : ℕ) (E : ℝ) (kj : k ≤ j) (Bn : 0 ≤ B)
      (BE : B ≤ E) (src : fare t k B) : fare t j E := by
    filter_upwards [src,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r atR rp x o fit
    exact (atR x o fit).trans (mul_le_mul_of_nonneg_right (wage_le kj Bn BE) (Real.rpow_nonneg rp.le _))
  obtain ⟨k,B,Bn,paid⟩ := pool fare widen (fun t=>WilsonCenteredNestedOrigin.original F Q hp fac foundation lo ticket h (axis S d t) Mn ηp)
  refine ⟨k,B,Bn,?_⟩
  filter_upwards [eventually_all.mpr paid] with r atR x o fit v
  rw [←chart F Q P h x o v,expand (older F P h x o (d:=d) - newer F Q h x o (d:=d)),mass,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun t _=>?_)
  rw [norm_smul,chart F Q P h x o]
  exact mul_le_mul_of_nonneg_left (atR t x o fit) (norm_nonneg _)

end YM.Integration.WilsonCenteredNestedShadowBasis

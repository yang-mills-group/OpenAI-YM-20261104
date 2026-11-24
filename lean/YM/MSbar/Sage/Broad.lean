import YM.MSbar.Sage.Wide
/-! Exponential radius even if retarget close to world. O(c) constant.Instance. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V U' V':Config G n}{x:Site n}{R:Rep G n}{σ C T a v δ w:ℝ}
open Finset RG.PathData
variable {Y X: Support n}{k M:ℕ}{p:BudgetPoint}
def silk (M:ℕ) (σ:ℝ)(Y: Support n) (x:Site n) := if x∈halo M Y then Real.exp (-σ/2*M) else Real.exp (-σ/2*M) * ∑ i∈Y, Real.exp (-(σ/2)*separation i x)
lemma silk_pos (M:ℕ) (σ:ℝ)(Y : Support n) (x:Site n) : 0≤ silk M σ Y x:=by unfold silk; split; positivity; exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun _ _=> (Real.exp_pos _).le)
def cape (n:ℕ)(σ:ℝ)(M:ℕ) := Real.exp (-σ/2*M)*(n:ℝ)*((2*M+1:ℝ)^4+81*meter (σ/2))
lemma silk_pays (M:ℕ) (h:0<σ)(Y:Support n): ∑ j,silk M σ Y j ≤ cape Y.card σ M:=by
    let E:=Real.exp (-σ /2*M); let Z j:= if j∈halo M Y then E else 0; let B x:=E * ∑ i∈Y,Real.exp (-(σ/2)*separation i x)
    have hp(j): silk M σ Y j ≤ Z j+B j:=by unfold B Z silk; split; exact le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (sum_nonneg fun _ _=> (Real.exp_pos _).le)); rw [zero_add]
    apply (sum_le_sum fun i _=>hp i).trans; rw [sum_add_distrib]
    have hx : (∑ j,Z j)=(halo M Y).card*E:=by
       calc _ = ∑ j∈halo M Y,Z j:= (sum_subset (subset_univ _) fun j _ h=> if_neg h).symm
            _ = _:= by rw [sum_congr (g:=fun _=>E) rfl (fun j hj=> if_pos hj),sum_const,nsmul_eq_mul]
    rw [hx]; unfold B; rw [← Finset.mul_sum,Finset.sum_comm]
    calc
       _ ≤ ((Y.card:ℝ)*(2*M+1:ℝ)^4)* E + E * ∑ i∈Y,(81*meter (σ/2)) := add_le_add (mul_le_mul_of_nonneg_right (by have hx:= Corona.halo_size Y M; rw [two_mul]; exact_mod_cast hx) (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> radial _ (half_pos h) _) (Real.exp_pos _).le)
       _ = _:= by unfold cape E; rw [sum_const,nsmul_eq_mul]; ring
lemma windmill (hy:x ∉ halo M Y)(y:Site n) (hp:y∈Y) (hr:0<σ)(d k:ℕ)(he:separation x y ≤ d+k): 1 ≤ Real.exp (σ*d)*Real.exp (σ*k)*silk M σ Y x:=by
    unfold silk; rw [if_neg hy]; let f i:= Real.exp (-(σ/2)*↑(separation i x)); have hi: M<separation y x:=lt_of_not_ge (fun h=>hy (halo_spec.mpr ⟨y,hp,h⟩))
    have hF:0 < σ/2:=half_pos hr
    apply le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (single_le_sum (s:=Y) (f:=f) (fun j _=> (Real.exp_pos _).le) hp) (Real.exp_pos _|>.le)) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)); unfold f; rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; apply Real.one_le_exp
    rw [separation_comm] at he
    have h₀:(separation y x:ℝ) ≤ d+k:=by exact_mod_cast he
    have h₁:(M:ℝ) ≤ separation y x:=by exact_mod_cast hi.le
    linarith only [mul_le_mul_of_nonneg_left h₀ hr.le,mul_le_mul_of_nonneg_left h₁ hr.le]
-- connector.Prices through Cut score. coefficients tap all lengths.
variable (A:Atom G k)(h:Place Y M U U' V V' p.threshold) (hr:0<σ)
def addOn (A: Atom G k)(p:BudgetPoint)(U V:Config G n)(x:Site n):= A.placed p U x-A.unmasked V x
def crownAtom (σ:ℝ) (k:ℕ) := (4:ℝ)*2^k*Real.exp (σ*8)
include h hr
lemma atom_mismatch : |addOn A p U U' x - addOn A p V V' x| ≤ A.budget σ*crownAtom σ k*silk M σ Y x:=by
    let a:=A.magnitude*2^k; have ha : 0≤ a:=by unfold a Atom.magnitude; positivity
    let f (U:Config G n) (W:Config G n):= addOn A p U W x; have hm(U V:Config G n): |f U V|≤ 2*a:=by
       apply (abs_sub _ _).trans; rw [two_mul]; exact add_le_add (A.placed_bound ..) (A.unmasked_bound ..)
    let L:= A.footprint x; have hp(y:Site n)(h:y∈L): separation x y ≤ A.length := Paths.where_slot x A.leg y ((Paths.atom_foot _ _ ) ▸ h)
    have hx: |f U U'-f V V'|≤ 4*a:=by linarith only [hm U U',hm V V',abs_sub (f U U') (f V V')]
    have hA :0 ≤ A.budget σ*crownAtom σ k*silk M σ Y x := by unfold Atom.budget Atom.magnitude crownAtom; have h:=silk_pos M σ Y x; positivity
    suffices H : f U U'=f V V' ∨ 1 ≤ Real.exp (σ*A.length)*Real.exp (σ*8)*silk M σ Y x by
       rcases H with he|he
       · change |f U U'-f V V'| ≤ _; rw [he,sub_self,abs_zero]; exact hA
       apply hx.trans ((le_mul_of_one_le_right (show 0≤4*a by positivity) he).trans_eq ?_); unfold a Atom.budget crownAtom; ring
    by_cases he:x∈halo M Y
    · unfold f; by_cases hk:A.length ≤ M
      · have ht : L⊆ halo (2*M) Y:= seep he (fun i hi=> (hp i hi).trans hk)
        have hK(U U':Config G n)(he: Healthy p.threshold (halo (2*M) Y) U)(hr:Agrees (halo (2*M) Y) U U'): addOn A p U U' x=0 :=by
           unfold addOn Atom.placed; rw [masked_eq _ _ _ _ (Finset.disjoint_of_subset_left ht he)]; exact sub_eq_zero.mpr (Extra.Iteration.Derivs.atom_local A x U U' (agrees_mono hr (coe_subset.mpr ht)))
        rw [hK U U' h.seals_old h.source,hK V V' h.seals_new h.sinks]; left; rfl
      right; unfold silk; rw [if_pos he, ← Real.exp_add, ← Real.exp_add]; apply Real.one_le_exp
      have hM: (M:ℝ) ≤ A.length:= by exact_mod_cast (le_of_not_ge hk) -- check
      linarith only [mul_le_mul_of_nonneg_left hM hr.le,hr,mul_nonneg hr.le (Nat.cast_nonneg (α:=ℝ) M)]
    by_cases hb: Disjoint (inspected L) Y
    · have hF :A.unmasked U' x=A.unmasked V' x:=Extra.Iteration.Derivs.atom_local A x _ _ (h.afterX _ (hb.mono_left (show L⊆ _ from subset_union_left)))
      have h': A.placed p U x=A.placed p V x:= ConnectedActivityE6.Raw.placed_local _ _ _ _ _ (h.old _ hb); unfold f addOn; rw [hF,h']; left; rfl
    obtain ⟨y,hy,hf⟩:= Finset.not_disjoint_iff.mp hb
    obtain ⟨i,hi,hx⟩:= halo_spec.mp (Next.Scheduling.flag_layer L hy)
    have ht:= windmill he y hf hr A.length 8 ((separation_triangle x i y).trans (Nat.add_le_add (hp i hi) hx))
    right; exact_mod_cast ht
end YM.MSbar.Heath

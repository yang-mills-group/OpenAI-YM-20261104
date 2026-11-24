import YM.FormalOPE.RG10.Position.Peal

/-!
# $g_X$ shift and preserving all positive-order position diagnoses on regulators (eventual m)

This is the common coupling chosen from the **connected** diagnostic of the positioned
real array (taking geometry-origin averages on each occurrence/moment, not an assertion that
it equals average-of-origin-level cumulants), with the accepted tensor choices and numerical
orientation/slope from Peal. It removes the order-zero contribution including any finite
lattice artifact. Still need RG11 agreement of the resulting first-order term to canonical
continuum first-order and estimates uniform enough in ensuing regulator limits (possibly after
an auxiliary coupling-shift), and then on the reading schedule.

Never claims nonsingularity on ALL q≥2; `Opens` is the exact rank condition, so use only with
that theorem in the chosen solver. Then `coin` etc give orders simultaneously and calibration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Peal
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} (F : Frames G){d k n : ℕ}
local notation "M" d => Mark (Deck F d) Profile.n
local notation "ι" => Fin 3
namespace Peal

def touch (a: (M 6) →fps) (x : Fin n ↪ ι) := ∑ s:Fin n → Deck F 6,
    C (∏ i,tune F (x i) (s i)) * a ⟨⟨n,near x⟩,s⟩
def single (i:ι) : Fin 1 ↪ ι := ⟨fun _=>i, fun _ _ _=> Subsingleton.elim _ _⟩
def together (a: (M 6) →fps) := touch F a (.refl (Fin 3))-(∑ i,touch F a (Fin.succAboveEmb i)*touch F a (single i)) + 2*∏ i:ι,touch F a (single i)
private lemma touch_maps (f : fps→+*fps)(hc : ∀ r:ℝ,f (C r)=C r) (a : (M 6) →fps) (x : Fin n ↪ ι) : touch F (f ∘ a) x=f (touch F a x):= by
 simp [touch,hc,map_sum,map_mul]
lemma together_maps (f : fps→+*fps)(hc : ∀ r:ℝ,f (C r)=C r) (a : (M 6) →fps) : together F (f ∘ a) = f (together F a) := by
 simp_rw [together,touch_maps F f hc,map_add,map_sub,map_mul,map_sum,map_prod,map_ofNat,map_mul]

def mint (a : (M 6) →fps) := C ((slope G)⁻¹) * deviation (together F a)
lemma mint_zero (a : (M 6) →fps) : constantCoeff (mint F a)=0:=by simp [mint]
def older (a : (M 6) →fps) := Triangle.inverseScale (mint F a)
def Xaction (a : (M 6) →fps) : fps →+* fps:= PowerSeries.substAlgHom (R:=ℝ) (Triangle.good (older F a) (inverse_zero _))
lemma action_on (a : (M 6) →fps)(f:fps) : Xaction F a f=subst (older F a) f:= congr_fun (coe_substAlgHom (R:=ℝ) (Triangle.good (older F a) (inverse_zero _))) f
lemma Opens_iff (a:(M 6) →fps)(h:G.Simple): coeff 1 (together F a)≠0 ↔ IsUnit (coeff 1 (mint F a)) := by
 simp [mint,pulse h|>.ne',Triangle.deviation,isUnit_iff_ne_zero]
lemma spends {a : (M 6) →fps} (h:G.Simple) (ht: coeff 1 (together F a)≠0) : mint F (Xaction F a ∘ a)=X := by
  let f:= Xaction F a
  have hc r:f (C r)=C r:= by rw [show _ = _ from action_on F _ (C r),subst_C]; rfl
  have he:= (Opens_iff F a h).mp ht
  calc
    _ = f (mint F a):= by
      change mint F (f ∘ a) = _; unfold mint; rw [together_maps _ f hc]; unfold Triangle.deviation; simp only [map_mul,map_sub,hc]; congr 3; rw [show constantCoeff (f _)= constantCoeff (subst (older F a) _) from congr_arg _ (action_on ..)]; exact Triangle.substitutes_zero (inverse_zero _)
    _ = _:= by unfold f; rw [action_on,older,inverseScale,dif_pos he]; exact (mint F a).subst_substInvOfIsUnit_right (mint_zero ..) he

end Peal

namespace Plan
variable (P : Plan F)

def coin (q:ℕ+) (m:ℕ) := mint F (P.dressed q m 6)
/-- `Mint`ed array at regulator, real, degree in g_X. Requires tested degree-one openness.
-/
def collect (q:ℕ+) (m d:ℕ) : (M d) →fps := fun v=>Xaction F (P.dressed q m 6) (P.dressed q m d v)

variable {F P} {q:ℕ+} (h : Official P.stock) (hq:1<q.val)
include h hq
lemma accumulate (hd:d ≤ k) : ∀ᶠ m in atTop,
    collect F P q m d= collect F P q m k ∘ ascend Profile.n (Deck.climb F hd) := by
  filter_upwards [shipped hq h hd] with m hm; unfold collect; conv_lhs => rw [hm.2]
  rfl
lemma objectives : ∀ᶠ m in atTop, ∀ r:ℕ, (P.stock d).select (fun v=> coeff r (collect F P q m d (markIn _ v))) = if r=0 then (P.stock d).target else 0:= by
 filter_upwards [proclaimed hq h d] with m he r
 unfold collect; let f:= P.dressed q m d; let a:=older F (P.dressed q m 6)
 simp_rw [action_on, AlignSeries.subst_finite (p:=older F (P.dressed q m 6)) (inverse_zero _)];
 let H:=(P.stock d)
 have hv : H.select (fun v=> ∑ k∈range (r+1), coeff k (f (markIn H.tests v))*coeff r (a^k)) = ∑ k∈range (r+1), coeff r (a^k) • H.select (fun v=>coeff k (f (markIn H.tests v))) := by
   calc
    _ = H.select (∑ k∈range (r+1), coeff r (a^k) • (fun v=>coeff k (f (markIn H.tests v)))):= by
        congr! 1; ext i; rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; exact mul_comm ..
    _ = _:= by rw [_root_.map_sum]; simp_rw [map_smul]
 change H.select _ = _
 rw [hv, sum_eq_single_of_mem 0 (mem_range.mpr (Nat.zero_lt_succ _))];
 · change _ • (P.stock d).select _ = _; rw [he]; simp
 intro k hk hw; change _ • (P.stock d).select _=_; rw [he,if_neg hw]; exact smul_zero _

/-- The degree-zero limit at any fixed horizon of these assigned fields. -/
lemma listening (v : Mark (Deck F d) Profile.n): Tendsto (fun m=> constantCoeff (collect F P q m d v)) atTop (𝓝 (Physical.free (L:=Maxwell.standard F) (deck F d) v)):= by
 let g e (z:M d) := constantCoeff (P.begins q e d z); let b:= Physical.free (L:=Maxwell.standard F) (deck F d)
 let A e i j := constantCoeff (P.poses q e d i j); let K := Physical.diag (Deck F d)
 have ht := tendsto_finsetSum (univ (α:=Fin v.1.n→ Deck F d)) (f:=fun i k=> (g k ⟨v.1,i⟩)*∏ j,A k (v.2 j) (i j)) (fun i _=> (starts (d:=d) hq P (Sigma.mk (β:=fun s:Profile=>Fin (Physical.Profile.n s)→Deck F d) v.1 i)).mul (tendsto_finsetProd _ fun _ _=>poses_zero hq h ..))
 -- change under function, geometric matrix
 apply ht.congr' ?_ |>.mono_right (le_of_eq ?_)
 · filter_upwards with m; unfold collect dressed g A; rw [action_on,older, Triangle.substitutes_zero (inverse_zero _), PertExtension.Position.insert_constant]; rfl
 congr 1; exact insert_one (J:=Deck F d) b v
omit h hq
variable (P)
lemma uses_axis (m) (h:G.Simple) (hq : coeff 1 (together F (P.dressed q m 6)) ≠ 0) : mint F (collect F P q m 6)= X := spends F h hq
end Plan
end YM.FormalOPE.RG10.Position

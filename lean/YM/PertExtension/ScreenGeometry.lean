import YM.PertExtension.MatrixFreeLeaf

/-! Placement near fixed scaled compact shapes after a common origin. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.PertExtension.LatticePT.Screens
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal RealInnerProductSpace FourierTransform
variable {G : Gauge}
variable {q : ℕ+}(hq:1<q.val)
local notation "reg" => (atTop : Filter ℕ)

def positiveLift (O : (t:ℕ)→Native q t) (t:ℕ) : Cover := fun i=>(O t i).val
def Placement (q:ℕ+)(O:ℕ→Cover):Prop:=∀ t i,((side q t).val:ℝ) /8 ≤ (O t i:ℝ) ∧ (O t i:ℝ)≤ 2*((side q t).val/8 : ℝ) -- Int→Real coercions
lemma placement (q)(O)(h:∀ t,O t ∈ origins q t): Placement q (positiveLift O):=by
  intro t i
  obtain ⟨ht,hy⟩:= (Finset.mem_filter.mp (h t)).2 i -- syntax
  have hd : 8∣(side q t).val:= ⟨q.val^(t+1)*q.val^(t^2),by change nativePeriod ..=_; unfold nativePeriod;ring⟩
  have hd := Nat.div_mul_cancel hd
  have he : ((side q t).val:ℝ)/8=buffer q t:= by apply (div_eq_iff_mul_eq (by norm_num)).mpr;exact_mod_cast hd
  unfold positiveLift
  rw [he];constructor
  · exact_mod_cast ht
  exact_mod_cast hy

variable (O : ℕ→Cover)(hO:Placement q O)
omit hO hq -- rebind

lemma small_offset (I:E4)(X : ℕ →Cover) {q : ℕ+}(hq:1<q.val) (h:Tendsto (fun t=> epsilon q t • mapZ (X t)) reg (𝓝 I))(i:Axis): ∀ᶠ t in reg,|(↑(X t i):ℝ)| ≤ ((side q t).val:ℝ)/24:= by
    let rho (t:ℕ):= epsilon q t; let M:= |I i|+1
    have hy : 0<M:=by dsimp [M];positivity
    have he : Tendsto ((EuclideanSpace.proj i : E4→L[ℝ] ℝ) ∘ fun t=>rho t • mapZ (X t)) reg (𝓝 (I i)):= (EuclideanSpace.proj i : E4→L[ℝ] ℝ).continuous.continuousAt.tendsto.comp h
    change Tendsto (fun t=> rho t * (X t i:ℤ)) _ _ at he
    have hh : ∀ᶠ t in reg, |rho t*(X t i:ℝ)| ≤ M:=he.abs.eventually (ge_mem_nhds (by unfold M; norm_num));
    let j (t:ℕ):=((side q t).val:ℝ)
    have hp: Tendsto (fun t=>24*M*(magnify q t/j t)) reg (𝓝 0):=by convert! (side_rate hq 1).const_mul (24*M) using 2 <;> simp [j]
    filter_upwards [hp.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)),hh] with k hk hB
    have hs:0 < rho k:=epsilon_pos ..
    rw [abs_mul,abs_of_pos hs] at hB
    have hK:24*M≤j k*rho k:= by
        have hg:0<j k:=by unfold j;exact Nat.cast_pos.mpr (side q k).pos
        have hr:magnify q k=(rho k)⁻¹:=by unfold rho;rw [epsilon,inv_inv] <;> rfl
        change 24*M*(magnify q k/j k) ≤ 1 at hk; rw [hr] at hk; field_simp [hg.ne', hs.ne'] at hk
        nlinarith only [hk,hg,hs]
    change 24 * M ≤ ((side q k).val:ℝ)*rho k at hK
    nlinarith only [hK,hB,hs]

variable {X X':ℕ→Cover}{z w:E4}
variable (hT:Tendsto (fun t=> epsilon q t • mapZ (X t)) reg (𝓝 z))
variable (hV:Tendsto (fun t=> epsilon q t • mapZ (X' t)) reg (𝓝 w))

def withOrigin (O:ℕ→Cover)(X:ℕ→Cover) t:=O t+X t

include hO hq hT hV
theorem sheltered (j j':Cover)(a : PlaqAxes) : ∀ᶠ t in reg, Screen (r:=1/8) (side q t) (reflectedOffset (withOrigin O X t) (withOrigin O X' t) j a j'):=by
 let i:Axis:=0; let Y:Cover:=j+j'+step a.val.1+ step a.val.2
 have hY : Tendsto (fun k=> epsilon q k • mapZ Y) reg (nhds 0) := by convert! (epsilon_zero hq |>.mono_right inf_le_left).smul_const (mapZ Y) using 2;simp -- zero_smul
 filter_upwards [small_offset z X hq hT i,small_offset w X' hq hV i,small_offset 0 (fun _=>Y) hq hY i] with t hX hX' hy
 refine ⟨i,?_⟩
 let s:= ((side q t).val:ℝ);
 have hs:0<s:=by unfold s;exact_mod_cast (side q t).pos
 have hz : ((reflectedOffset (withOrigin O X t) (withOrigin O X' t) j a j' i:ℤ):ℝ)/s= (((-(2*O t i+ (X t i + X' t i + Y i)):ℤ):ℝ))/s := by simp only [reflectedOffset,withOrigin,Y,Pi.neg_apply,Pi.add_apply,Pi.sub_apply];push_cast;ring
 unfold band;change 1/8≤ |_| ∧ |_|≤ (1-1/8 :ℝ);rw [hz];obtain ⟨ht,ht'⟩:=hO t i
 push_cast
 change s/8 ≤ (O t i: ℝ) at ht; change (O t i:ℝ)≤2*(s/8) at ht'; let D:=fun c:Cover=>(c i:ℝ)
 rw [abs_div, abs_of_pos hs, le_div_iff₀ hs,div_le_iff₀ hs,abs_le]
 suffices h:-(1-1/8)*s≤-(2*D (O t)+(D (X t)+D (X' t)+D Y))∧ -(2*D (O t)+(D (X t)+D (X' t)+D Y))≤ -(1/8)*s by
    change 1/8*s≤ |-(2*(O t i:ℝ)+((X t i:ℝ)+ (X' t i:ℝ)+(Y i:ℝ)))| ∧ (_∧_)
    exact ⟨le_abs.mpr (Or.inr (by dsimp [D] at *; linarith only [h.2])),by dsimp [D] at h; constructor <;> linarith only [h.1,h.2,hs]⟩
 dsimp [D]; obtain ⟨h₁,h₂⟩:=abs_le.mp hX; obtain ⟨H₁,H₂⟩:=abs_le.mp hX';obtain ⟨hn,hN⟩:=abs_le.mp hy; constructor <;> unfold s at * <;> linarith
end YM.PertExtension.LatticePT.Screens

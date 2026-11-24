import YM.RegulatorIR.Ledger.Terminal

/-! Lebesgue average versus full centered cell volume in four physical
coordinates. Half-open on integration variables. Accept tests with only
coefficient integrability. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Centered
open Topology Lattice MeasureTheory Set Metric Motion Spatial
open scoped ENNReal NNReal BigOperators Classical
variable {t l a C:ℝ} {x y o:Room}

def cube (x: Room)(t:ℝ) : Set Room := univ.pi fun i=> Ico (x i) (x i+t)
lemma inside : y ∈ cube x t ↔ ∀ i,x i≤y i ∧ y i < x i+t := by simp only [cube, Set.mem_pi,mem_univ,true_imp_iff,mem_Ico]
lemma seen (x:Room)(t:ℝ):MeasurableSet (cube x t) := MeasurableSet.pi (countable_univ) (fun _ _=> measurableSet_Ico)
lemma cubic (x:Room)(ht:0≤t):volume (cube x t)= ENNReal.ofReal (t^4) := by rw [cube,volume_pi,MeasureTheory.Measure.pi_pi]; simp_rw [Real.volume_Ico,add_sub_cancel_left]; simp [Axis,ENNReal.ofReal_pow ht]

def same (x:ℝ) : Room := fun _=> x
lemma drift (x:Room)(y:Room)(t:ℝ) (z:Room): z∈ cube x t ↔ y+z∈cube (y+x) t:=by simp only [inside, Pi.add_apply, add_le_add_iff_left, add_assoc, add_lt_add_iff_left]

def Rhythm (l:ℝ)(g: Room → ℝ) : Prop:= ∀ y: Cover,∀ x,g (slide l y + x)= g x

def accrue (g:Room→ℝ)(x:Room)(t:ℝ):= ∫ y in cube x t,g y
lemma periods {g:Room→ℝ}(H:Rhythm l g)(x:Room) (n:Cover) : accrue g (slide l n + x) l=accrue g x l:=by
 simp_rw [accrue, ← integral_indicator (seen ..)]
 let v:=slide l n
 rw [← integral_add_left_eq_self (μ:=volume) ((cube (v+x) l).indicator g) v]
 apply integral_congr_ae; filter_upwards with y
 by_cases he: y∈ cube x l
 · rw [indicator_of_mem ((drift x v l y).mp he), indicator_of_mem he, H]
 rw [indicator_of_notMem (fun h=>he ((drift x v l y).mpr h)),indicator_of_notMem he]

def weigh (x:Room) (t:ℝ)(g:Room→ℝ): ℝ := (accrue g x t) / t^4
lemma worth {g:Room→ℝ}(ht:0<t)(h:∀ y∈cube x t, ‖g y‖ ≤ C): ‖weigh x t g‖ ≤ C:=by
 rw [weigh,norm_div,Real.norm_of_nonneg (pow_nonneg ht.le _),div_le_iff₀ (by positivity)]; apply le_trans (norm_setIntegral_le_of_norm_le_const (f:=g) (show volume (cube x t)<⊤ by rw [cubic _ ht.le]; finiteness) h) ?_
 rw [Measure.real,cubic _ ht.le, ENNReal.toReal_ofReal (by positivity)]
lemma minusW {g h:Room→ℝ}(hg: IntegrableOn g (cube x t))(hh: IntegrableOn h (cube x t)) : weigh x t g-weigh x t h=weigh x t (fun w=> g w-h w):=by rw [weigh,weigh,weigh,accrue,accrue,accrue,integral_sub hg hh,sub_div]

abbrev Tiling (m:ℕ):= Axis→Fin m
def start (l d:ℝ){m:ℕ}(i:Tiling m): Room:=fun v=>d + ↑(i v).val*l
lemma place (b:ℤ){m:ℕ}(i:Tiling m): start l (t + b*l) i= slide l (fun v=> b + ↑(i v).val) + same t :=by ext1 v; simp [start,same]; ring
lemma periodized_c {g:Room→ℝ}(H:Rhythm l g)(o:ℝ)(n:ℤ){m:ℕ}(i:Tiling m): accrue g (start l (o+n*l) i) l = accrue g (same o) l:= by rw [place,periods H]

def block (l d:ℝ) (m:ℕ) : Set Room := ⋃ i:Tiling m,cube (start l d i) l
lemma block_meas (l d:ℝ) (m:ℕ) : MeasurableSet (block l d m):= MeasurableSet.iUnion fun _=> seen _ _
private lemma axis_sep {u v : ℕ}{l z w : ℝ}(hl:0<l)
   (h:w + ↑u*l ≤ z)(hh:z < w + ↑v*l + l): u ≤ v:=by
 by_contra! he
 have hA : (v:ℝ)+1 ≤ u := by exact_mod_cast he
 nlinarith only [hl,hA,h,hh]
lemma distinct {d:ℝ}(m:ℕ)(hl:0<l):Pairwise (Function.onFun Disjoint (fun i:Tiling m=> cube (start l d i) l)) :=by
 intro i j he; refine disjoint_left.mpr (fun {a} hp hx=> he ?_)
 ext1 v; obtain h₁:= inside.mp hp v; have h₂:= inside.mp hx v; exact Fin.ext (Nat.le_antisymm (axis_sep hl h₁.1 h₂.2) (axis_sep hl h₂.1 h₁.2))
lemma enclosure {d:ℝ}(m:ℕ)(hl:0<l)(he:a≤d)(hh:d+m*l≤a+t):block l d m ⊆ cube (same a) t:= by
 intro y h; obtain ⟨i,hi⟩:=mem_iUnion.mp h
 apply inside.mpr; intro v; obtain ⟨h₁,h₂⟩:= inside.mp hi v
 change a≤_ ∧ y v < a+t; unfold start at h₁ h₂
 have hv:((i v).val:ℝ)+1≤m:= by exact_mod_cast (show (i v).val+1≤m from (i v).isLt)
 constructor; exact he.trans ((le_add_of_nonneg_right (by positivity)).trans h₁);nlinarith

lemma block_vol (d:ℝ)(m:ℕ)(hl:0<l): volume.real (block l d m)=((m:ℝ)*l)^4:=by
 rw [block, measureReal_iUnion_fintype (distinct m hl) (fun _=> seen ..) (fun _=>by rw [cubic _ hl.le]; finiteness)]
 simp [Measure.real, cubic _ hl.le, ENNReal.toReal_ofReal (pow_nonneg hl.le _),Tiling, Axis,mul_pow]
lemma integrates {g:Room→ℝ}(H:Rhythm l g) (m:ℕ)(n:ℤ)(o:ℝ)(hl:0<l)(hp: IntegrableOn g (block l (o+n*l) m)): (∫ y in block l (o+n*l) m, g y) = (m:ℝ)^4 * accrue g (same o) l:=by
 rw [block, integral_iUnion (fun _=>seen ..) (distinct m hl) hp,tsum_fintype]
 change (∑ i:Tiling m, accrue g (start l (o+n*l) i) l)= _; simp [periodized_c H,Tiling,Axis]
end YM.RegulatorIR.Centered

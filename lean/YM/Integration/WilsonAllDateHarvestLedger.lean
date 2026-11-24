import YM.Integration.WilsonAllDateHarvestAffine
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Linear combination of the actual regular and forced inventories at the
same support, marker radius and support exponent. The majors are chosen
before all configurations. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestLedger

open Finset Lattice Wilson RG Marker MergeProof MergeProof.Accent Extra.Histories
open Push AbsoluteSums Ac GridApprox.Nil MeasureTheory Set
open scoped BigOperators Classical

variable {V I Y : Type*} [DecidableEq V] {J : Census V} {n : Side}
variable {w : V → ℝ} {S : I → Support n} {F H : I → Y → Poly J}
variable {B : ℕ} {α ρ σ : ℝ}

def linear (c d : ℂ) {E:Type*} [AddCommGroup E] [Module ℂ E] (a b:E) :=
  c • a + d • b

theorem towed (hF : Towed w S F B α ρ) (hH : Towed w S H B α σ) (c d : ℂ) :
    Towed w S (fun i U=>linear c d (F i U) (H i U)) B α (‖c‖*ρ+‖d‖*σ) := by
  obtain ⟨a,sa,ba,fa⟩:=hF
  obtain ⟨b,sb,bb,fb⟩:=hH
  refine ⟨fun i=>‖c‖*a i+‖d‖*b i,(sa.mul_left _).add (sb.mul_left _),?_,?_⟩
  · intro x
    convert budget_plus (budget_scale (norm_nonneg c) (ba x)) (budget_scale (norm_nonneg d) (bb x)) using 1
    ext i
    split_ifs <;> ring
  intro i
  obtain ⟨p,pp,hp,cp⟩:=fa i
  obtain ⟨q,pq,hq,cq⟩:=fb i
  refine ⟨fun z=>‖c‖*p z+‖d‖*q z,fun z=>add_nonneg (mul_nonneg (norm_nonneg _) (pp z))
      (mul_nonneg (norm_nonneg _) (pq z)),?_,?_⟩
  · intro U z
    change ‖c*(F i U).part z+d*(H i U).part z‖≤_
    refine (norm_add_le ..).trans ?_
    simp only [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hp U z) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hq U z) (norm_nonneg _))
  calc
    wordsPrice w (fun z=>‖c‖*p z+‖d‖*q z)=‖c‖*wordsPrice w p+‖d‖*wordsPrice w q := by
      unfold wordsPrice
      rw [mul_sum,mul_sum,←sum_add_distrib]
      exact sum_congr rfl fun z _=>by ring
    _ ≤ _:=add_le_add (mul_le_mul_of_nonneg_left cp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left cq (norm_nonneg _))

variable {G:Gauge} {o:V→Site n} {t:ℝ}

private theorem borne {p : Support n} {f g : Config G n → Poly J}
    (a : Borne o p f t) (b : Borne o p g t) (c d : ℂ) :
    Borne o p (fun U=>linear c d (f U) (g U)) t :=
  ⟨fun U V agree mark=>congrArg₂ (linear c d) (a.home U V agree mark) (b.home U V agree mark),
   fun z U=>congrArg₂ (linear c d) (a.turns z U) (b.turns z U),
   fun s=>((a.me s).const_mul c).add ((b.me s).const_mul d),
   fun U s absent=>by change c*(f U).part s+d*(g U).part s=0; rw [a.scope U s absent,b.scope U s absent]; ring⟩

private theorem either {E:Type*} [AddCommGroup E] [Module ℂ E] {x y:E} (c d : ℂ)
    (h : linear c d x y≠0) : x≠0 ∨ y≠0 := by
  by_contra! both
  exact h (by simp [linear,both])

private theorem many {x y:Poly J} (a:rises x) (b:rises y) (c d:ℂ) : rises (linear c d x y) := by
  intro s nz
  by_contra! short
  have cx:x.part s=0:=by by_contra h; exact (Nat.not_le_of_gt short) (a s h)
  have cy:y.part s=0:=by by_contra h; exact (Nat.not_le_of_gt short) (b s h)
  apply nz
  change c*x.part s+d*y.part s=0
  rw [cx,cy]
  ring

variable {H₀ H₁ : Support n → Config G n → Poly J} {K₀ K₁ : Box n → Config G n → Poly J}

theorem carton (a:Carton o H₀ K₀ t) (b:Carton o H₁ K₁ t) (c d:ℂ) :
    Carton o (fun i U=>linear c d (H₀ i U) (H₁ i U)) (fun i U=>linear c d (K₀ i U) (K₁ i U)) t := by
  constructor
  · intro i
    obtain ⟨x,mx⟩:=a.exp i
    obtain ⟨y,my⟩:=b.exp i
    refine ⟨⟨borne x.toBorne y.toBorne c d,fun U used=>
       (either c d used).elim (x.permits U) (y.permits U),?_⟩,fun U=>many (mx U) (my U) c d⟩
    intro U
    change c*(H₀ i U).part J.quiet+d*(H₁ i U).part J.quiet=0
    rw [x.sil U,y.sil U]
    ring
  · intro i
    obtain ⟨x,mx⟩:=a.flag i
    obtain ⟨y,my⟩:=b.flag i
    exact ⟨⟨borne x.toBorne y.toBorne c d,fun U used=>
      (either c d used).elim (x.permits U) (y.permits U)⟩,fun U=>many (mx U) (my U) c d⟩

theorem blend_eq {E:Type*} [AddCommGroup E] [Module ℂ E] (a b:E) (z:ℂ) :
    WilsonAllDateHarvestAffine.blend a b z=linear (1-z) z a b := by
  unfold WilsonAllDateHarvestAffine.blend linear
  rw [sub_smul,one_smul,smul_sub]
  abel

end YM.Integration.WilsonAllDateHarvestLedger

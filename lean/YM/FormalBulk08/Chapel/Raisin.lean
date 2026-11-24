import YM.FormalBulk08.Chapel.Tile

/-! Same-rate Taylor remainder. Impose width threshold as first condition on
block lengths. Kn estimates independent of L otherwise. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η C : ℝ}{m r:ℕ}{L : Side}{I J : Type}

-- peeling

def osc (σ:ℝ)(m:ℕ):= σ/((m:ℝ)+1)
def Threshold (σ η:ℝ)(m:ℕ)(L:Side):= η*m≤(L.val:ℝ)*(osc σ m/2)
lemma peel (m:ℕ)(h:0≤σ):osc σ m*m≤σ:= by
    have hx: (0:ℝ)<m+1:=by positivity
    calc _ ≤ osc σ m*(m+1):= mul_le_mul_of_nonneg_left (by linarith only) (div_nonneg h hx.le)
         _ = σ:= div_mul_cancel₀ _ hx.ne'
lemma osc_pos (m:ℕ)(h:0<σ):0<osc σ m:= div_pos h (by positivity)

def candor (S: Cross L I J)(x: Cover)(t:chain I m) := crown (fun _ : Fin m=>S) x t
def partD (S: Cross L I J)(x: Cover)(t:chain I m)(d:ℕ)(w : cloud m):= candor S x t w-party d (candor S x t) w
lemma ebb (L: Side)(j): (L.val:ℝ)⁻¹^j≤1:= pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast L.pos))

variable [Fintype I][Fintype J]
omit [Fintype I] in
lemma bells (h:0<σ)(_hs:0≤η)(hc:0≤C)(d:ℕ):∃ B:ℝ,0≤B∧∀ (L : Side),Threshold σ η m L→ ∀ k:ℕ,
    (k:ℝ)^d*(gold J L m k η C*(L.val:ℝ)⁻¹^d)≤ Real.exp (osc σ m*k) * (B*(L.val:ℝ)⁻¹^(m+d)) := by
    let M:ℝ:= m; let Y:=osc σ m
    have hy:0<Y:=osc_pos m h
    obtain ⟨B,hB,H⟩:= Cork.pockets d (show 0<Y/2 by positivity)
    let E:ℝ:=((Fintype.card J:ℝ)*C)^m;have he:0≤E:=pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hc) _
    refine ⟨B*Real.exp (M*η*8)*E,by positivity,fun L hw k=>?_⟩
    let a:ℝ:=L.val
    have ha:0<a:=by unfold a;positivity
    have ht : M*η*(k/a+8) ≤ Y/2*k+M*η*8 := by
       have hh : M*η/a≤ Y/2:= (div_le_iff₀ ha).mpr (by rw [mul_comm (Y/2),mul_comm M];exact hw)
       have he:=mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) k); ring_nf at he ⊢; linarith only [he]
    have hz : (k:ℝ)^d*Real.exp (M*η*(k/a+8))≤ Real.exp (Y*k)*(B* Real.exp (M*η*8)) := by
       apply (mul_le_mul (show (k:ℝ)^d ≤ B*Real.exp (Y/2*k) from (pow_le_pow_left₀ (by positivity) (by linarith only : (k:ℝ) ≤ 1+k) d).trans (H _ (Nat.cast_nonneg _))) (Real.exp_monotone ht) (Real.exp_pos _).le (by positivity)).trans_eq; rw [Real.exp_add];
       rw [show Y*(k:ℝ)=Y/2*k+Y/2*k by ring, Real.exp_add]; ring
    rw [gold,mul_pow, ←Real.exp_nat_mul, pow_add]; change k^d*(Real.exp (M*(η*(k/a+8)))* E*a⁻¹^m*a⁻¹^d) ≤ Real.exp (Y*k)*(B*Real.exp (M*η*8)*E*(a⁻¹^m*a⁻¹^d)) -- casts
    rw [←mul_assoc M η,←mul_assoc,←mul_assoc,←mul_assoc -- brittleness
        ]; grw [hz];ring_nf;exact le_rfl
-- remove G
lemma cash_part (h:0<σ)(hs:0≤η)(hc:0≤C)(d:ℕ): ∃ B:ℝ,0≤B ∧ ∀ (L : Side),Threshold σ η m L → Odd L.val → ∀ (S:Cross L I J), gauss S η C d → ∀ (x : Biglot I) t (w:cloud m) (u:Biglot J), Knoxville (fame _) η (piz L x u.2) (partD S x.1 t d w) (Real.exp (osc σ m * size w)*(B*(L.val:ℝ)⁻¹^(m+d))) := by
    obtain ⟨B,hB,H⟩:= bells (m:=m) (J:=J) h hs hc d
    refine ⟨B,hB,fun L hp ho S hS (x : Biglot I) t w u=>?_⟩
    let L0:= gold J L m (size w) η C * (L.val:ℝ)⁻¹^d; have hL : 0 ≤ L0:=by unfold L0 gold; positivity
    apply Knoxville.mono (B:=Real.exp (osc σ m * size w)*(B*(L.val:ℝ)⁻¹^(m+d))) _ (H L hp (size w)); refine climb_sharp L0 hL d w (fame J) (piz L x u.2) ?_
    intro v hv a ha; unfold L0; exact hv ▸ glutton hs hc S d hS ho x t (size w) u v hv.le a ha -- cast
lemma cash_cove (h:0≤η)(hc:0≤C)(d:ℕ) : ∃ B:ℝ,0≤B ∧ ∀ L (S:Cross L I J), gauss S η C d → Odd L.val→∀ (x: Biglot I) t (p:Grades (Fin m×Axis)), upper p ≤ d → ∀ u:Biglot J, Knoxville (fame _) η (piz L x u.2) (gang (candor S x.1 t) (roll p) 0) B := by
   let B:= (Real.exp (η*8) * ((Fintype.card J:ℝ)*C))^m
   refine ⟨B,by unfold B; positivity,fun L S hp he (x : Biglot I) t p hT u=>?_⟩
   apply (glutton h hc S d hp he x t 0 u (roll p) ((merch p).trans_le hT) 0 (by simp [Laurent.size])).mono
   simp only [gold, Nat.cast_zero, zero_div,zero_add]; have hx:0≤B:=by unfold B; positivity
   change B*_ * _ ≤ B; rw [mul_assoc]; exact mul_le_of_le_one_right hx (mul_le_one₀ (ebb ..) (by positivity) (ebb ..))
end YM.FormalBulk08.Chapel

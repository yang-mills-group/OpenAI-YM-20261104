import YM.Integration.WilsonOlderFreshGraphColumn
import YM.QuadraticLocal.Poetry.Volume

/-! The actual signed rooted link tensor becomes a one-name ink field. Its
separate mark at the original root survives even at angular rank zero. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphInk
open Function Filter Finset Lattice Laurent RG Wilson FormalBulk08 Reef Lava Lotus Shore Mesa Gorge Rift
open QuadraticLocal QuadraticLocal.Sunrise Push.AbsoluteSums AllOrder.Ink
open Primitives.TwoWave RealSlice
open scoped Classical ENNReal BigOperators Topology

def slip {ι₀:Type} {r:ℕ} (z:chain (Biglot ι₀) r) : Slip (Point (ι₀ ⊕ Unit)) :=
  (0,Sum.inr ()) :: List.ofFn (fun i=>( (z i).1,Sum.inl (z i).2))

def tensor {ι₀:Type} {r:ℕ} (T:Tile (Biglot ι₀) r) : AllOrder.Ink.Field (ι₀ ⊕ Unit) where
  Ty:=chain (Biglot ι₀) r
  fee:=T
  slip:=slip

theorem distinct {ι₀:Type} {r:ℕ} (z:chain (Biglot ι₀) r):
    Focus.Depicted ({()} : Finset Unit) (slip z) := by
  intro u
  cases u
  simp [slip,Focus.tally,Focus.calls,List.map_ofFn,Function.comp_def]

theorem meter_le {ι₀:Type} {r:ℕ} (o:ι₀) (z:chain (Biglot ι₀) r):
    meter (slip z) ≤ r * wide (fame ι₀) (Fin.cons (0,o) z : chain (Biglot ι₀) (r+1)) := by
  have one (j:Fin r):size (z j).1≤wide (fame ι₀) (Fin.cons (0,o) z : chain (Biglot ι₀) (r+1)):=by
    have h:=reached (fame ι₀) (Fin.cons (0,o) z : chain (Biglot ι₀) (r+1)) j.succ 0
    simpa [fame,capD] using h
  calc
    _ = ∑ j:Fin r,size (z j).1:=by simp [slip,meter,Laurent.size,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    _ ≤ ∑ _j:Fin r,wide (fame ι₀) (Fin.cons (0,o) z : chain (Biglot ι₀) (r+1)):= Finset.sum_le_sum fun j _=>one j
    _ = _ := by simp

theorem paid {ι₀:Type} [Fintype ι₀] {r:ℕ} {b a H:ℝ} (o:ι₀) (T:Tile (Biglot ι₀) r)
    (rent:Knoxville (fame ι₀) b (0,o) T H) (pos:0≤a) (strip:a*r≤b):
    (tensor T).Good a H (r+1) := by
  refine ⟨fun z=>by simp [tensor,slip],budget_of_sum (fun _=>by dsimp [Field.price,tensor];positivity) ?_⟩
  intro S
  apply (ENNReal.ofReal_le_ofReal_iff rent.1).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _=> Field.price_nonneg _ _ j)]
  refine (Finset.sum_le_sum fun z _=>?_).trans ((ENNReal.sum_le_tsum S).trans rent.2)
  have cap:a*↑(meter (slip z))≤b*↑(wide (fame ι₀) (Fin.cons (0,o) z : chain (Biglot ι₀) (r+1))):=by
    calc
      _≤a*(r*wide (fame ι₀) (Fin.cons (0,o) z : chain (Biglot ι₀) (r+1)):ℕ):=by
        apply mul_le_mul_of_nonneg_left _ pos
        exact_mod_cast meter_le o z
      _=a*r*↑(wide (fame ι₀) (Fin.cons (0,o) z : chain (Biglot ι₀) (r+1))):=by push_cast;ring
      _≤_:=mul_le_mul_of_nonneg_right strip (Nat.cast_nonneg _)
  dsimp only [Field.price,tensor]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [show ENNReal.ofReal |T z| = ‖T z‖ₑ by rw [←Real.norm_eq_abs,ofReal_norm]]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr cap)) _

/-- Mount the field at the indicated site on the same finite torus, with the
independent addressed probe on its own slot. -/
theorem site {ι₀:Type} [Fintype ι₀] {r:ℕ} (T:Tile (Biglot ι₀) r) (n:Side)
    (y:Site n) (A:Board ι₀ n ℝ) (x:Board Unit n ℝ):
    (tensor T).site n y (mingle A x) = x (y,()) * ∑' z:chain (Biglot ι₀) r,
      T z * ∏i:Fin r,A (y+wrap n (z i).1,(z i).2) := by
  rw [Field.site,←tsum_mul_left]
  apply tsum_congr
  intro z
  change T z * invoice y (slip z) (mingle A x) = _
  simp [slip,invoice,AllOrder.Ink.paid,stood,mingle,List.map_ofFn,Function.comp_def,List.prod_ofFn,mul_left_comm]

def all {ι₀:Type} {cap:ℕ} (T:∀r:Fin (cap+1),Tile (Biglot ι₀) r.val):AllOrder.Ink.Field (ι₀ ⊕ Unit):=
  Field.sum (fun r=>tensor (T r))

theorem purchased {ι₀:Type} [Fintype ι₀] {cap:ℕ} {a b:ℝ} (o:ι₀)
    (T:∀r:Fin (cap+1),Tile (Biglot ι₀) r.val) (C:Fin (cap+1)→ℝ)
    (wallet:∀r,Knoxville (fame ι₀) b (0,o) (T r) (C r)) (pos:0≤a) (strip:a*cap≤b):
    (all T).Good a (∑r,C r) (cap+1) ∧ ∀z,Focus.Depicted ({()} : Finset Unit) ((all T).slip z) := by
  refine ⟨Field.keep _ (fun r=>(paid o (T r) (wallet r) pos ?_).debt le_rfl le_rfl ?_) ?_,
    fun z=>distinct z.2⟩
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt_succ r.isLt) pos).trans strip
  · omega
  · exact budget_finite (fun r=>(wallet r).1) le_rfl

end YM.Integration.WilsonOlderFreshGraphInk
end

import YM.Integration.WilsonMeasuredRelativePair
import YM.Lattice.Support

/-! Short paths for the relative residual of two independently placed genuine children. -/

namespace YM.Integration.WilsonRelativeChildRoute

open Lattice
open scoped Classical

private lemma route_length (u v : Cover) (K : ℕ)
    (hv : ∀ i, (v i - u i).natAbs ≤ K) :
    (route u v 1).length ≤ 4*K := by
  have bound (l : List Axis) : (axisRoute u v l).length ≤ l.length*K := by
    induction l with
    | nil => simp [axisRoute]
    | cons a l ih =>
      change (straight a (v a - u a) ++ axisRoute u v l).length ≤ (l.length+1)*K
      rw [List.length_append,Nat.add_mul,one_mul,add_comm (l.length*K)]
      exact Nat.add_le_add (by simpa [straight] using hv a) ih
  simpa [route,allAxes] using bound (allAxes 1)

/-- The actual fine endpoint, including the two different signed child residues. -/
theorem original {c n : Side} (g : Ratio c n) (y z : Site n) :
    ∃ w : Walk,
      stop (g.embed (g.parent z)) w = z-(y-g.embed (g.parent y)) ∧
      w.length ≤ 4*g.count.val := by
  let b := g.embed (g.parent z)
  let u := lift b
  let t := lift (g.residue z) - lift (g.residue y)
  let v := u+t
  refine ⟨route u v 1,?_,?_⟩
  · have hw := congrArg (wrap n) (route_end u v 1)
    rw [wrap_stop_cover] at hw
    have hu : wrap n u = b := wrap_lift _
    rw [hu] at hw
    have residue (x : Site n) : wrap n (lift (g.residue x)) = x-g.embed (g.parent x) :=
      eq_sub_iff_add_eq.mpr (by rw [add_comm,g.unpack_at])
    rw [hw]
    change wrap n (u + (lift (g.residue z) - lift (g.residue y))) = _
    rw [map_add,map_sub,hu,residue,residue]
    dsimp only [b]
    abel
  · apply route_length
    intro a
    have hz := lift_centers (g.residue z) a
    have hy := lift_centers (g.residue y) a
    have hh : |lift (g.residue z) a - lift (g.residue y) a| ≤ (g.count.val : ℤ) :=
      abs_le.mpr ⟨by omega,by omega⟩
    rw [← Int.natCast_natAbs] at hh
    change ((u a+(lift (g.residue z) a - lift (g.residue y) a)) - u a).natAbs ≤ _
    rw [add_sub_cancel_left]
    exact_mod_cast hh

/-- The physical length is measured at the original spacings of this fixed run. -/
theorem measured (S : Schedule) {m N : ℕ} (h : m ≤ N) (p : ℕ) (y z : Site (S.side N p)) :
    let g := S.toDepth h p
    ∃ w : Walk,
      stop (g.embed (g.parent z)) w = z-(y-g.embed (g.parent y)) ∧
      S.a N*(w.length : ℝ) ≤ 4*S.a m := by
  obtain ⟨w,hend,hw⟩ := original (S.toDepth h p) y z
  refine ⟨w,hend,?_⟩
  have hr : (w.length : ℝ) ≤ 4*((S.toDepth h p).count.val : ℝ) := by exact_mod_cast hw
  calc
    S.a N*(w.length : ℝ) ≤ S.a N*(4*((S.toDepth h p).count.val : ℝ)) :=
      mul_le_mul_of_nonneg_left hr (S.a_pos N).le
    _ = 4*S.a m := by rw [← S.embeds_scale (S.toDepth h p)]; ring

end YM.Integration.WilsonRelativeChildRoute


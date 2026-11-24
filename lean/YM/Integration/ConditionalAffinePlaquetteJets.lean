import YM.Integration.PhysicalAffineScalarTails
import YM.Integration.ConditionalAffineRouteJets

/-! Full-minus-cut original signed plaquette jets after restriction to the
actual stored coarse copy. A local uniform series argument supplies the
finite-order smoothness used by the coordinate restriction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffinePlaquetteJets
open Function Filter Set Metric Lattice Wilson RG Precision Exterior Tree Matrix Pressure Pressure.Tube
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open Push.Uniform Push.AbsoluteSums FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalAffineScalarUncut.PathTail
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (s : Signed)

/-- Smoothness at the real joint input before restricting its cohort of
independent coarse derivatives. -/
theorem smooth (W : PathData G) (i : Cell f) (R d n : ℕ) (hd : 0<d)
    {p : Clip} {σ C Λ : ℝ} (hW : W.Bounds p σ C Λ) :
    ContDiffAt ℝ n (fun z => W.ell (signedFine F z s) i - Pressure.shorten W R d (signedFine F z s) i) 0 := by
  obtain ⟨Z,hZ⟩ := paint_supply G (n+1)
  let w := tailWeight W i R d
  let a := W.row i.2
  let M := rootsCost G Z (σ/2) (n+1)
  let Q j := (|w j| *Real.exp ((σ/2)*(a j).2.length))*M
  have hM : Summable Q := (tail_budget W i R d hd hW).2.1.mul_right M
  have hwidth := width_positive (half_pos hW.width) (n+1) S.ratio.count
  let u (j : ℕ) (z : Positions (Joint F G)) := w j • (a j).2.atSite (signedFine F z s) i.1
  have hj (j : ℕ) (z : Positions (Joint F G)) (hz : z∈ball 0 1) : Allows (n+1) (u j) z (Q j) := by
    obtain ⟨D,hD,hv⟩ := piece F s hZ z (show ‖z‖≤1 from (show ‖z‖<1 by simpa using hz).le)
      i.1 (a j).2 (half_pos hW.width) (w j)
    exact hD.mono ((le_mul_of_one_le_right hD.nonneg (Real.one_le_exp (by positivity))).trans hv)
  have eq : (fun z => W.ell (signedFine F z s) i - Pressure.shorten W R d (signedFine F z s) i) = fun z => ∑' j, u j z :=
    funext fun z => (removed W i R d hW (signedFine F z s)).symm
  rw [eq]
  exact (ConditionalAffineSeries.sum_smooth isOpen_ball (convex_ball (0:Positions (Joint F G)) 1).isPreconnected hM hj).contDiffAt
    (ball_mem_nhds _ (by norm_num))

def copy : Vec G c 1 →L[ℝ] Positions (Joint F G) :=
  (paint F G).symm.toContinuousLinearMap.comp ((plain G c 1).toContinuousLinearMap.prod (0 : Vec G c 1 →L[ℝ] AxisChart G F))

def primary (i : raw G c) : Primary c G := ((i.1,i.2.1),i.2.2)

private theorem ray_copy (i : raw G c) : copy F (ray G c i)=bolt (.inl (primary i)) := by
  funext z
  cases z with
  | inl q =>
    change (ray G c i) (q.1.1,q.1.2,q.2) = (bolt (ι:=Joint F G) (Sum.inl (primary i))) (Sum.inl q)
    by_cases h : q=primary i
    · subst q
      rcases i with ⟨y,a,t⟩
      simp [primary,ray,bolt]
    have h' : (q.1.1,q.1.2,q.2)≠i := fun he => h (congrArg primary he)
    simp [ray,bolt,h,h']
  | inr q =>
    change 0=(bolt (ι:=Joint F G) (Sum.inl (primary i))) (Sum.inr q)
    simp [bolt]

include F

theorem smooth_raw (W : PathData G) (i : Cell f) (R d n : ℕ) (hd : 0<d) {p : Clip} {σ C Λ : ℝ}
    (hW : W.Bounds p σ C Λ) : ContDiffAt ℝ n (fun B => W.ell (shone S s B) i-Pressure.shorten W R d (shone S s B) i) 0 := by
  let U := fun z => W.ell (signedFine F z s) i-Pressure.shorten W R d (signedFine F z s) i
  have he : (fun B => W.ell (shone S s B) i-Pressure.shorten W R d (shone S s B) i) = U ∘ copy F := by
    funext B
    change _ = W.ell (signedFine F (coarseCopy F B) s) i - Pressure.shorten W R d (signedFine F (coarseCopy F B) s) i
    rw [same_field s F B]
  rw [he]
  have hU : ContDiffAt ℝ n U (copy F (0:Vec G c 1)) := by
    rw [map_zero]
    exact smooth F s W i R d n hd hW
  exact hU.comp (0:Vec G c 1) (copy F).contDiff.contDiffAt

/-- Exponential error at the original fine plaquette, with coarse-site
labels retained after applying the physical replica/forest coordinates. -/
theorem price (W : PathData G) (i : Cell f) (R d n : ℕ) (hd : 0<d) {p : Clip} {σ C Λ Z : ℝ}
    (hW : W.Bounds p σ C Λ) (hs : PaintSupply G n Z) {k : ℕ} (hk : k≤n) (l : Fin k→ raw G c) :
    let α := entryWidth n S.ratio.count (σ/2)
    let y := affine s 0 i.1
    Real.exp (α*Stars.rays (native c) (S.ratio.parent y) (hearth ∘ l))*
      ‖iteratedFDeriv ℝ k (fun B => W.ell (shone S s B) i - Pressure.shorten W R d (shone S s B) i) 0 (ray G c ∘ l)‖ ≤
      Real.exp (α*k)*((Real.exp (-(σ/2)*((R:ℝ)/d))*C)*rootsCost G Z (σ/2) n) := by
  intro α y
  let U := fun z => W.ell (signedFine F z s) i - Pressure.shorten W R d (signedFine F z s) i
  let l' : Fin k→Joint F G := fun a => Sum.inl (primary (l a))
  let D := spanSites (address F G) y l'
  let D' := Stars.rays (native c) (S.ratio.parent y) (hearth ∘ l)
  let P := (Real.exp (-(σ/2)*((R:ℝ)/d))*C)*rootsCost G Z (σ/2) n
  have he : (fun B => W.ell (shone S s B) i - Pressure.shorten W R d (shone S s B) i) = U ∘ copy F := by
    funext B
    change _ = W.ell (signedFine F (coarseCopy F B) s) i - Pressure.shorten W R d (signedFine F (coarseCopy F B) s) i
    rw [same_field s F B]
  have hj : iteratedFDeriv ℝ k (U∘copy F) 0 (ray G c∘l)=Push.Uniform.entry U 0 l' := by
    rw [Next.Foundations.jets_linear (copy F) (smooth F s W i R d k hd hW),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    unfold Push.Uniform.entry
    apply congrArg
    funext a
    exact ray_copy F (l a)
  have H : ‖Push.Uniform.entry U 0 l'‖≤P*Real.exp (-α*D) := (PhysicalAffineScalarUncut.PathTail.price F s W i R d hd hW hs 0 (mem_ball_self (by norm_num))) k hk l'
  have hα := width_positive (half_pos hW.width) n S.ratio.count
  have hsep (a : Fin k) : (separation (S.ratio.parent y) ((l a).1):ℝ) ≤ separation y (S.ratio.embed (l a).1)+1 := by
    have HH := Corona.foreshorten S.ratio y (S.ratio.embed (l a).1)
    rw [S.ratio.embed_parent] at HH
    have hL : (0:ℝ)<S.ratio.count.val := by exact_mod_cast S.ratio.count.property
    have hL' : (1:ℝ)≤S.ratio.count.val := by exact_mod_cast S.ratio.count.property
    have hb : (S.ratio.count.val:ℝ)*separation (S.ratio.parent y) (l a).1 ≤
        (separation y (S.ratio.embed (l a).1):ℝ)+S.ratio.count.val := by exact_mod_cast HH
    calc
      _ ≤ ((separation y (S.ratio.embed (l a).1):ℝ)+S.ratio.count.val)/S.ratio.count.val :=
        (le_div_iff₀ hL).2 (by simpa only [mul_comm] using hb)
      _ ≤ _ := by rw [add_div,div_self hL.ne']; exact add_le_add (div_le_self (Nat.cast_nonneg _) hL') le_rfl
  have hd' : D'≤(D:ℝ)+k := by
    unfold D' Stars.rays D spanSites
    simp only [Nat.cast_sum]
    change (∑ a : Fin k,(separation (S.ratio.parent y) (l a).1:ℝ)) ≤
      (∑ a : Fin k,(separation y (S.ratio.embed (l a).1):ℝ)) + (k:ℝ)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      (Finset.sum_le_sum (s:=Finset.univ) fun a _ => hsep a)
  rw [he,hj]
  apply (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left hd' hα.le)) (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left H (Real.exp_pos _).le).trans_eq
  rw [mul_left_comm,←Real.exp_add,show α*((D:ℝ)+k)+ -α*D=α*k from by ring]
  ring

end YM.Integration.ConditionalAffinePlaquetteJets

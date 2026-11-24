import YM.X.Plate.Grain
import YM.X.Shelf.Corn
import YM.PertExtension.TopCalibration
/-!
# Head-degree component of genuine radial cover mark. λ-jets under dilation without truncation.^Tensor channels. Exact degree, uniform Frame slot count.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal LiftMark MvPolynomial Function Filter Metric Asymptotics
open Reed Source PertExtension LatticePT Stems Shelf Gauss Braid Plate Grow
open Heat.Top
open scoped Topology ContDiff BigOperators Pointwise Classical
open ProjectorNext.Calibration
variable {G:Gauge} {d n m k:ℕ} {V W I:Type*} {F: Labels.Frame G d}
local notation "K"=> Kite (Okay G)
local notation "H"=> Hair G
local notation "ℓ"=> Curly G
abbrev HC {V:Type*} (p:poly V)(d:ℕ):= IsWeightedHomogeneous (fun _ : V=> (1:ℕ)) p d
lemma leafy {p:poly V}: HC p d ↔ cut d p=p:= ⟨(IsWeightedHomogeneous.weightedHomogeneousComponent_same ·),fun h=> by rw [← h]; exact weightedHomogeneousComponent_mem ..⟩
lemma HCglyph (f:V→₀ℂ): HC (glyph f) 1 := by
    unfold Normal.glyph; simp_rw [Finsupp.linearCombination_apply, Finsupp.sum]; refine IsWeightedHomogeneous.sum _ _ _ ?_; intro i hi; rw [← C_mul']; exact (isWeightedHomogeneous_X ..).C_mul _ 
lemma cut_swap (c: W→V→₀ℂ)(p:poly W): cut d (exchange c p)= exchange c (cut d p):= Maxwell.Free.commuting _ _ _ (fun i=> Normal.exchange_x c i ▸ HCglyph (c i)) p d
lemma cut_loom (q:poly (Atom G))(k:ℕ): cut k (Stems.loom q)= loom (cut k q):= cut_swap _ _
lemma hc_eval {p:Curly G}(h:∀ (t:ℝ) (A:Brush G), snap (t • A) p=(t:ℂ)^d • snap A p): HC p d:= by
   intro a ha; let F:= factors (V:=Hair G) (2:ℂ); have he:F p = (2:ℂ)^d • p:= by
      apply snap_ext; intro x; rw [map_smul,show (2:ℂ)= Complex.ofReal 2 by norm_num, ← h 2 x]; refine DFunLike.congr_fun (f:=(snap x).comp F) ?_ p; ext1 i; unfold snap F text; simp
   have hh:= congr_arg (coeff a) he; simp only [F,factors,Perch.jets_coeff, coeff_smul, smul_eq_mul] at hh; have ht:= mul_right_cancel₀ ha hh; apply Nat.pow_right_injective (by norm_num : 2≤2); dsimp only; exact_mod_cast ht
lemma markHC (S:CoverConfig G→ℝ)(h:Small G S) : HC (mark S h k) k:= by
   obtain ⟨b,h⟩:=h; refine hc_eval (fun t x=>?_); simp only [mark_test, stamp_at h]; rw [show comb (t • x)=t • comb x from rfl,PertExtension.Series.Radial.jet_smul]; push_cast; rfl
open Labels
lemma labelHC (p:Label G d)(h:p∈Grade (k,m)): HC p.val m:= by
   intro a ha; have ht:= (pure_grade _ _).1 h ha; rw [Labels.weight_slot] at ht; simpa [Finsupp.weight_apply,smul_eq_mul] using! congr_arg Prod.snd ht
lemma labelCount (p:Labels.Label G d)(h:p∈Grade (k,m))(hp:p≠0): 2*m≤ k:= by
   have he : p.val ≠0 := fun h=> hp (Subtype.ext h); obtain ⟨a,ha⟩:= p.val.support_nonempty.mpr he
   have hh:= mem_support_iff.mp ha; obtain hm:= labelHC p h hh; have hn:= (pure_grade _ _).1 h hh; rw [weight_slot] at hn; rw [← hm, ← show Finsupp.weight Labels.generation a=k from congr_arg Prod.fst hn]; simp_rw [Finsupp.weight_apply,nsmul_eq_mul,Finsupp.sum, mul_one]; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; unfold generation; nlinarith -- nat
lemma slotCount (i:F.Index): 2*(F.grades i).2≤ (F.grades i).1:= labelCount _ (F.pure i) (F.basis.ne_zero i)
lemma raw_z (p:Word G): duty (bookMark p n) (p.d/2+n):= by
   unfold bookMark; refine duty.costs _ (fun i _=> ?_); apply duty.scalar; let m:=(p.F.grades i).2+n; let P:= hut n p i; have ht : HC P m:= markHC _ (opt i p.sound p.chosen); refine (duty.more (k:=m) ?_ ?_); · change duty P m; rw [← leafy.mp ht]; exact cut_bound m P
   unfold m; have hh:= slotCount i; have he:= p.F.bound i; omega
lemma cut_thermal (A:Symmetric V)(p:poly V)(he:duty p k): cut k (milk A p)=cut k p:= by
    rcases Nat.eq_zero_or_pos k with h|h; · rw [(Heat.degree_decrease A p k he).1 h]
    have hx : (milk A p-p).totalDegree<k:= (Heat.degree_decrease A p k he).2 h; rw [← sub_eq_zero,← map_sub,cut_cap _ hx]
lemma cut_bounds (A:Symmetric H) (p:Word G): cut (p.d/2+n) (milk A (bookMark p n))= cut (p.d/2+n) (bookMark p n):= cut_thermal _ _ (raw_z p)
end YM.PositionX.Tri

import YM.RG12.Roof.Layout
/-!
# Leading dilation coupling on filtration-compatible, nonredundant pivots

Includes actual Book mirrors and any DiffPlan Inclusions. An adapter
from horizon-by-horizon k measurements to real tested-step estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Roof
open Function Filter Set Finset Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East Extra.FD
open Arche Shapes RG12.Frames Maxwell OPE
variable {G:Gauge}{C:Family G}{M:∀ d, ℕ→RepChart C d}
set_option quotPrecheck false
local notation "A" => C.path.levels
local notation "F!"=> standard C
variable {S : Table C.book}{f:Extraction.Order}(U:Final C f S)(d:ℕ)
local notation "P!"=> U.sector.derivatives
local notation "V!"=>Desk.Sector (P!) d
local notation "X!"=>RG12.Frames.Col (V!)
local notation "T!"=> glint U d
local notation "TY"=>Free.scheme C.labels

abbrev code (i:Frames.Grade d) : (V!) i→ₗ[ℂ] C.label i := ((F!).representative _).comp (cones U i i le_rfl)
def jaw (M:∀ d,ℕ→RepChart C d)(k:ℕ)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)): (X!)→ₗ[ℂ] S.Field d := ∑ i:Frames.Grade d, ((P!).rise i.is_le) ∘ₗ glowH M k (Z i) ∘ₗ code U d i ∘ₗ (LinearMap.proj i)
-- ambiguity with Weather etc
lemma jaw_len (M:∀ d,ℕ→RepChart C d)(k:ℕ)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i))(x:(X!)):
  jaw U d M k Z x= ∑ i, (P!).rise i.is_le (glowH M k (Z i) (code U d i (x i))):=by simp only [jaw,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
lemma piece (M:∀ d,ℕ→RepChart C d)(k:ℕ)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)) (i:Frames.Grade d)(v:(V!) i):
  jaw U d M k Z (Frames.put (V!) i v)=(P!).rise i.is_le (glowH M k (Z i) (code U d i v)):=by
    rw [jaw_len, sum_eq_single i]; simp only [Frames.put, Pi.single_eq_same]
    · intro j _ h
      rw [show Frames.put (V!) i v j=0 from Pi.single_eq_of_ne h _,map_zero,map_zero,map_zero]
    simp
lemma aim (Q:Prescription (P!))(hQ:Q.Coherent)(M:∀ d,ℕ→RepChart C d)(k:ℕ)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)): Frames.triangular (V!) ((Desk.official Q hQ d).symm.toLinearMap.comp (jaw U d M k Z)):=
    Desk.compatible Q hQ d U.room.kernel.laws.toSymmetric U.phase.transport.injection _ (fun i x=>⟨_,(piece U d M k Z i x).symm⟩)

lemma honor (x:(X!)): (T!) x = ∑ i:Grade d,(TY).rise i.is_le ((F!).project i (code U d i (x i))):=by
    nth_rw 1 [←RG12.Frames.by_grade (V!) x,map_sum]
    apply sum_congr rfl; intro i _
    have he: (F!).project (↑i) (code U d i (x i))=cones U i i le_rfl (x i):= Table.rep ..
    rw [listL,he]
    unfold cones lane; simp only [LinearMap.comp_apply]
    change (TY).rise _ _= (TY).rise _ ((TY).rise le_rfl _)
    rw [(TY).arrival (table_sym _) (Free.scheme_filters _)]

private lemma brush (ax:Axis)(N:ℕ)(s:ℝ)(hs:0<s)(M:∀ d,ℕ→RepChart C d)(k:ℕ)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i))(v w:(X!)):
    illumination S U.room.kernel.spin d d ax N s (jaw U d M k Z v) (jaw U d M k Z w) = ∑ i:Grade d,∑ j:Grade d, illumination S U.room.kernel.spin _ _ ax N s (glowH M k (Z i) (code U d i (v i))) (glowH M k (Z j) (code U d j (w j))):=by
   rw [jaw_len,jaw_len,map_sum (illumination S U.room.kernel.spin d d ax N s),LinearMap.sum_apply]
   simp_rw [map_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
   exact lifts d U.room.kernel.spin _ _ _ _ _ hs _ _ (P!) U.room.kernel.laws.toSymmetric U.phase.transport.injection U.phase.transport.rights i.is_le j.is_le -- U binder explicit?

private lemma brush_free (ax:Axis)(N:ℕ)(s:ℝ)(hs:0<s)(v w:(X!)):
    polished C.labels d d ax (N:ℝ)⁻¹ s ((T!) v) ((T!) w) = ∑ i:Grade d,∑ j:Grade d, polished C.labels i j ax (N:ℝ)⁻¹ s ((F!).project i (code U d i (v i))) ((F!).project j (code U d j (w j))):=by
   rw [honor,honor]
   unfold polished
   rw [map_sum,map_sum,LinearMap.sum_apply]
   apply sum_congr rfl;intro i _; rw [map_sum]; apply sum_congr rfl; intro j _
   apply lights d i j s (N:ℝ)⁻¹ ax hs

-- given oriented comparisons from k-rank kernels (D=d)
abbrev CastH (ax:Axis)(N:ℕ)(g t s:ℝ)(M:∀ d,ℕ→RepChart C d)(k:ℕ)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)) : Prop :=
    ∀ (i j:Fin (d+1))(v:C.label i)(w:C.label j),
    ‖illumination S U.room.kernel.spin i j ax N t (glowH M k (Z i) v) (glowH M k (Z j) w) - polished C.labels i j ax (N:ℝ)⁻¹ s ((F!).project i v) ((F!).project j w)‖ ≤ g*mass C i v * mass C j w
private lemma fee : ∃ K:ℝ,0≤K∧∀ (i:Grade d)(v:(X!)), mass C i (code U d i (v i)) ≤ K*‖v‖:=by
   let Z(i:Grade d) := ((code U d i).comp (LinearMap.proj i : (X!)→ₗ[ℂ] (V!) i)).toContinuousLinearMap -- notation?
   let k(i:Grade d):= (↑((C.labels.level i).extra+1):ℝ)*‖Z i‖; let K:= ∑ i,k i
   have hK i : 0 ≤ k i:=by unfold k;positivity
   refine ⟨K,sum_nonneg (fun i _=>hK i),fun i v=> ?_⟩
   apply (mass_le_norm ..).trans (le_trans (b:=k i*‖v‖) ?_ (mul_le_mul_of_nonneg_right (single_le_sum (f:=k) (fun i _=>hK i) (mem_univ _)) (norm_nonneg _)))
   unfold k; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact (Z i).le_opNorm _

-- compatible assembly before dilation (norm scaling at braces)
theorem bundled : ∃ J:ℝ,0≤J ∧ ∀ (ax:Axis)(N k:ℕ)(M:∀ d,ℕ→RepChart C d)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)){g t s:ℝ},0≤g → 0 < t → 0<s→CastH U d ax N g t s M k Z →∀ (v w:(X!)),
    ‖illumination S U.room.kernel.spin d d ax N t (jaw U d M k Z v) (jaw U d M k Z w)-polished C.labels d d ax (N:ℝ)⁻¹ s ((T!) v) ((T!) w)‖ ≤ J*g*‖v‖*‖w‖:=by
    obtain ⟨K,hK,h⟩:=fee U d
    refine ⟨(↑d+1)^2*K^2,by positivity,fun ax N k M Z g t s hg ht hs hA v w=>?_⟩
    rw [brush U d ax N t ht,brush_free U d ax N s hs,← sum_sub_distrib]
    simp_rw [← sum_sub_distrib]
    apply (norm_sum_le ..).trans; let I:= Grade d
    -- align constant sum
    let Y:=g*(K*‖v‖)*(K*‖w‖)
    apply le_trans (b:=∑ i:I, ∑ j:I, Y)
    · refine sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (fun j _=> (hA i j _ _).trans (by have hx:=mass_nonneg C i (code U d i (v i)); have hy:= mass_nonneg C j (code U d j (w j)); unfold Y;exact mul_le_mul (mul_le_mul_of_nonneg_left (h ..) hg) (h ..) hy (by positivity)))))
    simp only [sum_const,card_univ,Grade,I,Fintype.card_fin,Y,nsmul_eq_mul]; push_cast; exact le_of_eq (by ring)

private lemma range_pad (s:ℝ)(x:(X!))(hs:1 ≤ s): ‖RG12.Frames.dilate s x‖ ≤ s^d*‖x‖:=by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hs) _) (norm_nonneg _))] -- test
    intro i; rw [dilation,norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hs) _)]
    exact mul_le_mul (pow_le_pow_right₀ hs i.is_le) (norm_le_pi_norm x i) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hs) _)

-- protect engineering power for each illuminated **pivot**. enough accuracy for polynomial log
-- geometry (where moving geometry input available). Not enough per dyadic step for sharp across.
local notation "SQ"=>RG12.Desk.Paired.sampleForm
abbrev white (ax:Axis)(N:ℕ)(v w:(X!)) := polished C.labels d d ax (N:ℝ)⁻¹ 1 ((T!) v) ((T!) w)
theorem thermal : ∃ J:ℝ,0≤J ∧ ∀ (ax:Axis)(N k:ℕ)(M:∀ d,ℕ→RepChart C d)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)){g t s:ℝ},0 ≤ g → 0 < t → 1 ≤ s →CastH U d ax N g t s M k Z →∀ (v w:(X!)),
    let x:=jaw U d M k Z ∘ₗ Frames.dilate s
    ‖illumination S U.room.kernel.spin d d ax N t (x v) (x w)-white U d ax N v w‖ ≤ J*g*s^(2*d)*‖v‖*‖w‖:=by
    obtain ⟨J,hJ,h⟩:= bundled U d; refine ⟨J,hJ,fun ax N k M Z g t s hg ht hs hp v w=>?_⟩
    let V:=Desk.Sector (P!) d; let v':=dilate (V:=V) s v; let w':=dilate (V:=V) s w
    have he:=h ax N k M Z hg ht (zero_lt_one.trans_le hs) hp v' w'; have hh := real_exact (C:=C) d ax (N:ℝ)⁻¹ s (zero_lt_one.trans_le hs).ne' ((T!) v) ((T!) w)
    rw [show (T!) v'=Pert.Scale.gear C.labels d s ((T!) v) from dim U d s v,show (T!) w'=Pert.Scale.gear C.labels d s ((T!) w) from dim U d s w,hh] at he
    intro x; apply he.trans
    apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left (range_pad U d s v hs) (mul_nonneg hJ hg)) (range_pad U d s w hs) (norm_nonneg _) (mul_nonneg (mul_nonneg hJ hg) (mul_nonneg (pow_nonneg (zero_le_one.trans hs) _) (norm_nonneg _))))
    rw [two_mul,pow_add]; exact le_of_eq (by ring)

lemma whitened : ∃ J:ℝ,0≤J ∧ ∀ (ax:Axis)(N k:ℕ)(M:∀ d,ℕ→RepChart C d)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)){g t s:ℝ},0 ≤ g → 0 < t → 1 ≤ s →CastH U d ax N g t s M k Z →∀ (v:(X!)),
    let x:=jaw U d M k Z ∘ₗ Frames.dilate s
    |(SQ U (Shapes.scope ax N) d t).eval (x v)-(white U d ax N v v).re| ≤ J*g*s^(2*d)*‖v‖^2:=by
    obtain ⟨J,hJ,h⟩:=thermal U d; refine ⟨J,hJ,fun ax N k M Z g t s hg ht hs hp v=>?_⟩
    intro x
    have he:= counted U ax d (x v) N 1 t;change (SQ U _ d ((t*(1:ℕ):ℝ))).eval _= _ at he
    rw [Nat.cast_one,mul_one] at he
    rw [he,← Complex.sub_re]; rw [sq,← mul_assoc]; exact (Complex.abs_re_le_norm _).trans (h ax N k M Z hg ht hs hp v v)

lemma base (ax:Axis): ∃ K:ℝ,1 ≤ K ∧∀ᶠ N:ℕ in atTop, ∀ v, let b:=(white U d ax N v v).re
    b ≤ K*‖v‖^2∧‖v‖^2 ≤ K*b:=by
   obtain ⟨c,K,hc,hK,h⟩:= worthwhile C.labels d ax (P:=1) le_rfl
   let e:= LinearEquiv.ofBijective (glint U d) (glinted U d); let q:= (LinearEquiv.toContinuousLinearEquiv (𝕜:=ℂ) e)
   let X := ‖q.toContinuousLinearMap‖; let Y := ‖q.symm.toContinuousLinearMap‖
   refine ⟨max 1 (max (K*X^2) (Y^2/c)),le_max_left ..,?_⟩
   filter_upwards [h] with N h v b; let x:= glint U d v
   obtain ⟨he,hp⟩:= (show c*‖x‖^2 ≤ b ∧ b≤K*‖x‖^2 from h 1 (Set.mem_Icc.mpr ⟨le_rfl,le_rfl⟩) _)
   have hx:‖x‖ ≤ X*‖v‖:= q.toContinuousLinearMap.le_opNorm _
   have hy:‖v‖ ≤ Y*‖x‖:=by have h:=q.symm.toContinuousLinearMap.le_opNorm (q v); change ‖q.symm (q v)‖ ≤ Y*‖x‖ at h; rwa [q.symm_apply_apply] at h -- test
   constructor
   · refine hp.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) (zero_le_one.trans hK)).trans ?_); rw [mul_pow,←mul_assoc]; exact mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (sq_nonneg _)
   apply (pow_le_pow_left₀ (norm_nonneg _) hy 2).trans
   rw [mul_pow]; have hh:0 ≤ b:=(mul_nonneg hc.le (sq_nonneg _)).trans he
   refine le_trans (b:=Y^2/c*b) ?_ (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) hh)
   rw [div_mul_eq_mul_div,le_div_iff₀ hc]; nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg Y)]
end YM.RG12.Roof

import YM.OPE.Compatible.Chain.Maul
/-!
# downstream local curvature charge from full unconstrained boost. Dual lower.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06 Work.F08
variable {C:KernelChoices}{r:ℕ}
lemma uphill {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](P:Law E)(v:Dual' E)(x:E): 2*v x-P.P x x≤ v (P.inverse v):=by
      let y:=P.inverse v; obtain ⟨c,hc,H⟩:= P.slope; have hh:= H (y-x); have hw:=mul_nonneg hc.le (sq_nonneg ‖y-x‖); have hp:P.P y x=v x:=DFunLike.congr_fun (P.applies _) x; rw [map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply,P.turns x y,hp, show P.P y y=v y from DFunLike.congr_fun (P.applies _) y] at hh; change _≤v y; linarith only [hh,hw]
variable (H:Even n.val){J:Type}[Fintype J]
local notation "TK" => Libra.Keys G (Limb H)
def pointD (p: J→edgeV n)(w: Keys G J)(i:Limb H): G.Color := ∑ j, if pathX H (p j)=i then (if dir H (p j) then -w j else w j) else 0
def pointS (p:J→edgeV n)(w:Keys G J):Dual' TK := ∑ j:J,∑ i:G.ColorIndex,(w j i:ℝ) • (MarkC H i (addressR (p j)))
-- inertia exact if members distinct
lemma parcelled (p:J→edgeV n)(w: Keys G J)(h:Injective (pathX H ∘ p))(j:J): hover H (pointD H p w) (p j)=w j:=by
     have hp : pointD H p w (pathX H (p j))= if dir H (p j) then - w j else w j:=by
          unfold pointD; rw [sum_eq_single_of_mem j (mem_univ j) (fun b _ hv=> if_neg (show pathX H (p b) ≠ pathX H (p j) from h.ne hv)),if_pos rfl]
     unfold hover; rw [hp]; cases ht:dir H (p j)<;>simp
lemma parade (o: edgeV n)(u:TK)(i:G.ColorIndex): MarkC H i (addressR o) u=(hover H u o) i:=by rcases o with ⟨o,a⟩;change (cloak H u (o,coord a)) _=_; rw [cloak_at]
abbrev picture (w:Keys G J) := ∑ i:J,‖w i‖^2
lemma point_bal (p:J→edgeV n)(w: Keys G J)(h:Injective (pathX H ∘ p)): PressX H (pointD H p w)= picture w∧ pointS H p w (pointD H p w)= picture w:=by
     let f:= pathX H ∘ p;constructor
     · let x(i:Limb H):= ‖pointD H p w i‖^2; rw [show PressX H (pointD H p w)=∑ i,x i from rfl,← sum_subset (Finset.subset_univ (Finset.univ.image f)), sum_image h.injOn]; swap
       · intro i _ hi; unfold x pointD; rw [sum_eq_zero]; simp; intro j _; rw [if_neg]; intro hh; exact hi (mem_image.mpr ⟨j,mem_univ _,hh⟩)
       apply Finset.sum_congr rfl; intro i hi; have he:= parcelled H p w h i; unfold x; rw [← he]
       unfold hover; split; next ht=>rw [norm_neg]; rfl
       next ht=> rfl
     unfold pointS; simp only [LinearMap.sum_apply,LinearMap.smul_apply,parade,parcelled H p w h,smul_eq_mul]; unfold picture; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]; simp [pow_two]
lemma ascent (v:Train r)(hx:4 ≤ r)(p:J→edgeV n)(w: Keys G J)(h:Injective (pathX H ∘ p)){b:ℝ}(hb:0<b)(ht:∀ x:TK,(boost H v hx C).P x x≤ b* PressX H x): b⁻¹* picture w≤ (boost H v hx C).wick (pointS H p w) (pointS H p w):=by
      let u:= pointD H p w; let P:=boost H v hx C (G:=G); let f:=pointS H p w; have hk:= point_bal H p w h; have hp:= uphill P f (b⁻¹ • u); have he:= ht u; change b⁻¹ * _ ≤ f (P.inverse f)
      apply le_trans _ hp; rw [map_smul,map_smul,map_smul]; change _ ≤ 2*(b⁻¹*f u)- b⁻¹*(b⁻¹*P.P u u); rw [show f u= _ from hk.2]
      have hu:P.P u u ≤ b*picture w:= he.trans_eq (congr_arg _ hk.1); grw [hu]; apply le_of_eq; field_simp; ring
end YM.OPE.Cascade.Terp

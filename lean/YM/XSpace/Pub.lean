import YM.XSpace.TiltRank
import YM.XSpace.Output1
/-!
# Usable result in odd channel. Completely eliminates need to compute sym changes on cut annuli.

The sufficient hypotheses here use the independent position graph. No flow inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.AxesTangent
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick Normalize Structure1 Cirrus Future Photo PowerSeries Retirement
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}(W:Initialize G)(V:Store G)(d:ℕ) {n:ℕ}(p:Tags G d n)(c:Shade.Cut)
lemma lively (z:Cirrus.Sample n): live W d z 0 (hinge d ∘ p)= live W d z 0 p:=by
  have he(m:Mesh)(D:Fin n→ℕ)(p q:∀ i, HP G (D i))(h:∀ i,(q i).val=Taylor.mirror _ (p i).val)(x:Fin n→m.Sites): coeff 0 (W.atTuple m D x q)= coeff 0 (W.atTuple m D x p):=by simp_rw [Initialize.atTuple_eq,fun i=> splinted (h i) m W (x i),← map_prod, Bare.reverse_normalized,coeff_rescale,pow_zero,one_mul]
  rw [live,lite,lite]; exact Finset.sum_congr rfl fun i _=> he _ _ (fun k=> Normalize.part d (i k) (p k)) _ (fun k=> hinge_part ..) _
lemma TriG (A:Change G d): A.val∈ Tri G d:= (tri_may _).2 ⟨A.property.1,A.property.2.1⟩
def inequality (a:ℝ) : FieldEnd G d:= (harvest W c d a).val + (-1:ℂ) • ready W c a d
lemma still_tri (a:ℝ): inequality W d c a∈ Tri G d:= Submodule.add_mem _ (TriG _ _) (Submodule.smul_mem _ _ (ready_in W c a d)) -- incl d?
def smallCharge (a:ℝ): Odds G d:= ⟨_,pass_in _ (still_tri W d c a)⟩
lemma myCommand (i:Sample n): records W d (ready W c (unit i) d) i p - fallRecords W d c i p=lot (live W d i 0) (inequality W d c (unit i)) p:=by simp_rw [fallRecords,records,sub_apply,inequality,map_add,map_smul,add_apply,smul_apply,neg_one_smul]; ring
lemma readyCost (x: Points n)(h:x∈Good c n): Likely (Gate x) (fun i=> adequate W (ready W c (unit i) d) (unit i) i.layout p):=by
  apply (established W c d (stepG x) (Eventually.of_forall unit_pos) charts x.ofLp p (aims x (beyond_conf c h)) (beyond_ok c h)).congr; filter_upwards with i; rw [show i.layout= (fun j=> home i+charts i j) from funext fun j=>by unfold charts; abel]; rw [adequate, adequate, reply_plus, blossom_plus]
lemma readyCost' (x: Points n)(h:x∈Good c n): Likely (Gate x) (fun i=> records W d (ready W c (unit i) d) i p):=by
  obtain ⟨y,hy⟩:= readyCost W d p c x h; have hz:=Bloom.spends x (adjusted_cost W d p x _ (start_cost W c d (stepG x) (Eventually.of_forall unit_pos))); have ht:= hz.add hy; rw [zero_add] at ht; exact ⟨_,ht.congr (fun i=> sub_add_cancel ..)⟩
lemma passBudget (H: Manages c G d) : Still ℂ Front (fun m=> smallCharge W d c m.spacing):=by
  let s (p:PotLin G d) (m:Mesh):= live W d (ascend p.w m) 0; let A m:= inequality W d c m
  apply Earned H _ s (fun p _ hp=> (notices W d hp p.w p.h).comp (points_at p.w)); intro p h
  have ht(x): Likely (Gate p.w) (fun i=> lot (live W d i 0) (A (unit i)) x):=by simp_rw [A,← myCommand]; exact (readyCost' W d x c p.w h).sub (structures W d c x p.w h)
  have he(x): Likely Front (fun m=> lot (s p m) (A m.spacing) x):=by obtain ⟨b,hb⟩:= ht x; exact ⟨_,hb.comp (points_at p.w)⟩
  change Likely _ (fun i=> lot (s p i) (passT _) _); simp_rw [passT,map_smul,map_add, map_smul, smul_apply, add_apply, smul_apply,pass_into _ p.p (s p _) (fun q=> lively W d q _)]; exact Likely.smul (Likely.const ..) (Likely.add (he _) (Likely.smul (Likely.const ..) (he _)))

-- remove fully in odd-null tangent diagnostic at point level
variable (hx: Manages c G d) (H:Granted V d c) (x: Points n)(h:x∈Good c n)(U:SlotOdd p)(L:∀ X∈ Tri G d,lot (scene x d) X p=0)
include hx h U L in
lemma scaledOut : Tendsto (fun i=> lot (live W d i 0) (inequality W d c (unit i)) p) (Gate x) (𝓝 0):=by
  let t(i:Sample n):= smallCharge W d c (unit i); let D:PotLin G d:= ⟨n,p,x,beyond_conf c h⟩; let f (i:Sample n):= meters D (live W d i 0)
  obtain ⟨T,hT⟩:= passBudget W d c hx; let B:=Module.finBasis ℂ (Odds G d); have ht(i): lot (live W d i 0) (inequality W d c (unit i)) p= ∑ j,B.coord j (t i) * f i (B j):=by
    rw [pass_even _ _ _ (fun q=> lively W d q i) U]; change f i (t i)=_; conv_lhs=> rw [← B.sum_repr (t i),map_sum]; skip
    simp [map_smul,Module.Basis.coord_apply]
  have he(j): Tendsto (fun i=> f i (B j)) (Gate x) (𝓝 0):=by change Tendsto (fun i=> lot (live W d i 0) (B j).val p) (Gate x) _; rw [← L (B j).val (B j).property.1]; simp_rw [lots]; exact tendsto_finsetSum _ fun i _=> notices W d _ x D.h
  simp_rw [ht]; have hs:=tendsto_finsetSum Finset.univ (fun j _=> (show Tendsto (fun i=>B.coord j (t i)) _ _ from (hT (B.coord j)).comp (liftG x)).mul (he j)); simpa only [mul_zero,Finset.sum_const_zero] using hs
include H hx U L h in
theorem removes : Tendsto (fun i=>adequate W (ready W c (unit i) d) (unit i) i.layout p) (Gate x) (𝓝 (checked1 W V d x p)):=by
  let A i:= ready W c (unit (n:=n) i) d; let b:= (fallFee W V d c).val; have ht: checked1 W V d x p= orderBasic W d c x p:= by
    have hb: b∈ Tri G d:= TriG d _; rw [independent W V d c H x h, calibrate]; change _+lot _ b p=_; rw [L b hb,add_zero]; rfl
  rw [ht]; have hs:= Bloom.spends x (adjusted_cost W d p x A (start_cost W c d (stepG x) (Eventually.of_forall unit_pos))); have hu:= scaledOut W d p c hx x h U L; simp_rw [← myCommand] at hu; let v:= fallRecords W d c (n:=n); have hf:=maturation d p _ (structures W d c) x h; have hp:= (hf.add hu).sub hs; rw [sub_zero,add_zero] at hp; exact hp.congr fun _=> by abel
end YM.XSpace.AxesTangent

import YM.Contacts.Revest.Purity
import YM.Contacts.Junction.Reception
/-! Support estimates for the model labels. Full valid invoice (E parts);
 quantitative β-quietness of all models; projection needs this extra residual. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Revest.Tucks
open Function Filter Set Finset Lattice RG Ovens Pressure Wilson MeasureTheory
open AnalyticBridge VerifiedReset PhysicalNext.Repeat Trio Next.Scheduling Clock Model Arbor Province.Costing
open Push.AbsoluteSums Animals Precision Milling Milling.Steam Pulse Extra.Iteration Quotes Flute
open Junction Junction.Buyer
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {n:Side} {B:BudgetPoint} {f g : ℝ} {k i j:ℕ} {G :Gauge}
variable {t a d v ε s C Λ u w :ℝ}
section sample
variable {V W: Trio.Offer G n}(h:Flute.Salary B V C)
include h
lemma grow (hE:C≤ t): Salary B V t:= by obtain ⟨u,hu,hQ⟩:=h.tariff; exact {h with tariff:=⟨u,hu,fun x=> (Cost.enlarge (hQ x) hE)⟩}
lemma small (a:ℝ): Salary B (a • V) (|a| *C):= by
   obtain ⟨u,hu,hQ⟩:=h.tariff; refine ⟨fun _ _ _ _=>congr_arg (a • ·) (h.move_ ..),fun x=>CouplingShape.reg_scale _ (h.bill x),fun x=> by simp [h.zen], fun x hx i j hi hj=> ?_, ⟨_,fun x=>CouplingShape.sup_scale a (hu x), anchored_scale (abs_nonneg _) hQ⟩⟩
   have ht:logHessian ((a • V) x) i j=a * logHessian (V x) i j:= by unfold logHessian; change iteratedFDeriv ℝ 2 (a • (V x ∘ increment 1)) 0 _=_; rw [iteratedFDeriv_const_smul_apply (CouplingShape.flat_C2 (h.bill x))]; rfl
   rw [ht,h.erase x hx i j hi hj,mul_zero]
lemma debit (hW:Salary B W t):Salary B (V-W) (C+t):= by
   obtain ⟨u,hu,hQ⟩:=h.tariff; obtain ⟨v,hv,hV⟩:=hW.tariff; refine ⟨fun _ _ _ _=> congr_arg₂ (·-·) (h.move_ ..) (hW.move_ ..),fun x=>CouplingShape.reg_sub (h.bill x) (hW.bill x), fun x=>by simp [h.zen,hW.zen], fun x hx i j hi hj=> ?_, ⟨u+v,fun x=>CouplingShape.sup_sub (h.bill x) (hW.bill x) (hu x) (hv x),fun x=> ?_⟩⟩
   · erw [Pi.sub_apply,hessian_sub (h.bill x) (hW.bill x),h.erase x hx i j hi hj,hW.erase x hx i j hi hj,sub_self]
   exact Eq.mp (by simp only [mul_add, Pi.add_apply, BudgetPoint.mass,ite_add_zero]) (budget_plus (hQ x) (hV x))
lemma debt (a:ℝ)(_he:0≤a)(hf:C≤a):Salary B (-V) a:= by simpa only [abs_neg,abs_one,one_mul,neg_smul,one_smul] using (small (grow h hf) (-1))
lemma add (hv:Salary B W t): Salary B (V+W) (C+t):= by simpa using debit h (small hv (-1))
omit h
lemma sum {ι:Type*} (x:Finset ι)(V:ι→Offer G n)(b:ι→ℝ)(H:∀ i∈x,Salary B (V i) (b i)): Salary B (∑ i∈x,V i) (∑ i∈x,b i):= by
   induction x using Finset.induction_on with
   | empty=> rw [sum_empty,sum_empty]; refine ⟨fun _ _ _ _=>rfl,fun x=> Progress.DirectedRecipe.unspent B _,fun x=>rfl,fun x _ a b _ _=> hessian_zero 0 a b,0,fun x=>Progress.DirectedRecipe.no_cost B _ _, fun x=>?_⟩; simp [SumBudget,BudgetPoint.mass]
   | insert i x hi ih=> rw [sum_insert hi,sum_insert hi]; exact add (H i (mem_insert_self ..)) (ih (fun j hj=> H j (mem_insert_of_mem hj)))
end sample
abbrev ε₀:ℝ:= (1/40:ℝ)
abbrev mileage (x:ℝ)(p:Stage)(i:ℕ):ℝ:= Real.exp (p.supportExponent*81)*x^(Sienna.vow* Arbor.hero i+ ε₀)
-- width stages.
lemma tavern (x:ℝ){T:PathData G}{F:bore G}{p:Stage}(hh:Time.Same p B)(hz:10*B.B<n.val)(H:Charted G k x B T F p.clip d v ε₀ i j):
     Salary B (Buyer.book (f:=n) k B F p.clip T i) (mileage x p i):= by
   let C:= x^(Sienna.vow*hero i+ ε₀); refine ⟨Model.reflects _ H.connected.1,H.sector n, fun i=> (H.hull n i).2,fun x _=> H.projection n hz x, fun _=>C,H.funds n hz, fun x=>?_⟩
   refine ⟨fun i=> ?_,Summable.of_finite,?_⟩
   · dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (H.funds n hz x).1; exact le_rfl
   change (∑' i:Site n, if i=x then _ else 0)≤_
   rw [tsum_fintype, Finset.sum_ite_eq',if_pos (Finset.mem_univ _)]
   refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (H.funds n hz x).1
   rw [← hh.2.2]; apply mul_le_mul_of_nonneg_left _ B.exponent_pos.le; exact_mod_cast ((Corona.cover_mono (show neighbors B.B x ⊆ halo (1*B.B) {x} from (fun v hv=> halo_spec.mpr ⟨x,by simp,((neighbors_mem ..).mp hv).trans_eq (one_mul _).symm⟩)) B.B).trans (Corona.tile x 1 B.B B.B_pos)) -- orientation
section dynamics
-- formula coefficient | log x |> order. mask attached. includes all i≤k as used by Junction
abbrev coef (β:ℝ)(i:ℕ):= β * (gap β)^i
def integrated (B:BudgetPoint)(F:bore G)(p:Clip)(T:PathData G)(k:ℕ)(β:ℝ): Offer G n:= ∑ i∈Finset.range (k+1), coef β i • Buyer.book k B F p T i
-- trivials: adaptation,local for Poetry.
def written (B:BudgetPoint)(F:bore G)(p:Clip)(T:PathData G)(k:ℕ)(β:ℝ) : Story G:= ∑ i∈Finset.range (k+1), coef β i • Province.slice k B.B T F p i
lemma codify (B:BudgetPoint)(F:bore G)(p:Clip)(T:PathData G)(k:ℕ)(β:ℝ): pass (written B F p T k β) n=integrated B F p T k β:= by ext x u; unfold written integrated Model.pass; simp only [Finset.sum_apply,Pi.smul_apply]; rfl
abbrev tint (i:ℕ):ℝ:= 1- (i:ℝ)/2
abbrev ect (b C:ℝ)(i:ℕ):ℝ:= if 0 ≤ tint i then C^(tint i) else b^(tint i)
private lemma power {x:ℝ} (h:0<x)(i:ℕ): coef x i=x^(tint i):= by
   unfold coef; have hz : gap x=x^(-(1/2):ℝ):= by rw [gap,Real.sqrt_eq_rpow,Real.rpow_neg h.le]
   unfold tint; rw [hz,← Real.rpow_natCast ((x:ℝ)^(-(1/2):ℝ)) i, ← Real.rpow_mul h.le, show (1:ℝ)-(i:ℝ)/2 = 1+(-(1/2):ℝ)*(i:ℝ) from by ring,Real.rpow_add h,Real.rpow_one]
private lemma boxMeter {x c u C:ℝ}(hx:0<x)(hu:0<c)(ht:c*x≤u)(hv:u≤C*x)(i:ℕ): |coef u i|≤ ect c C i*x^(tint i):= by
    have hb:0<u:=(mul_pos hu hx).trans_le ht; have hC :0<C:=(mul_pos_iff_of_pos_right hx).1 (hb.trans_le hv); rw [power hb,abs_of_pos (Real.rpow_pos_of_pos hb _)]; unfold ect; split;
    next ha=> exact (Real.rpow_le_rpow hb.le hv ha).trans_eq (Real.mul_rpow hC.le hx.le)
    next ha=> exact (Real.rpow_le_rpow_of_nonpos (mul_pos hu hx) ht (le_of_not_ge ha)).trans_eq (Real.mul_rpow hu.le hx.le)
abbrev broker (i:ℕ)(c:ℝ):ℝ:= |tint i| * c^(tint i-1)
private lemma barometer {x c u v:ℝ}(hx:0<x)(hc:0<c)(hu:c*x≤u)(hv:c*x≤v)(i:ℕ): |coef u i - coef v i| ≤ |u-v| * (broker i c*x^(tint i-1)):= by
  let a:= tint i; let S:=Set.Ici (c*x); let f(x:ℝ):=x^a; have h (x:ℝ)(he:x∈S):0<x:=(mul_pos hc hx).trans_le he
  have he:= (convex_Ici (𝕜:=ℝ) (c*x)).norm_image_sub_le_of_norm_deriv_le (f:=f) (fun x he=> (Real.hasDerivAt_rpow_const (Or.inl (h x he).ne')).differentiableAt) (C:=broker i c * x^(tint i-1)) (fun y hy=>?_) hv hu; swap
  · rw [(Real.hasDerivAt_rpow_const (p:=a) (Or.inl (h y hy).ne')).deriv,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.rpow_pos_of_pos (h y hy) _)]; unfold broker; rw [mul_assoc, ← Real.mul_rpow hc.le hx.le]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply Real.rpow_le_rpow_of_nonpos (mul_pos hc hx) hy; unfold a tint; have := Nat.cast_nonneg (α:=ℝ) i; linarith
  rw [power (h u hu),power (h v hv),mul_comm]; exact he
local notation "ε'" => (-(23/20):ℝ)
local notation "θ" => (-(43/20):ℝ)
private lemma hero_earn (i:ℕ): tint i+ Sienna.vow*hero i+ ε₀< ε':= by
   unfold tint Sienna.vow ε₀; by_cases hi:i<3
   · interval_cases i <;> norm_num [hero]
   have hx:= Nat.cast_le (α:=ℝ).mpr (owned i); have hv:= Nat.cast_le (α:=ℝ).mpr (show 3 ≤ i from (by omega)); norm_num1 at *; linarith
-- compare all β in wider interval. charge w. Domain p being stage geometry. tiny asympt each. reserve bound ~ x^-1.15
lemma baker (k:ℕ) (p:Stage) (c C:ℝ) (hp:0<c): ∀ᶠ x:ℝ in atTop,∀ (n:Side) (B:BudgetPoint) (T:PathData G) (F:bore G),Time.Same p B → 10*B.B<n.val→ ∀ (d v:ℝ)(j:ℕ), (∀ i≤k,Charted G k x B T F p.clip d v ε₀ i j)→∀ u∈ Set.Icc (c*x) (C*x), ∀ w∈ Set.Icc (c*x) (C*x), Salary B (integrated (n:=n) B F p.clip T k u) (x^ε') ∧ Salary B (integrated (n:=n) B F p.clip T k u - integrated (n:=n) B F p.clip T k w) (|u-w| * x^θ):= by
   let a := Finset.range (k+1)
   let X (s:ℝ) (x _i:ℝ):=x^s
   let b (x:ℝ)(i) := ect c C i*x^(tint i)*mileage x p i; let f (x:ℝ)(i):= broker i c*x^(tint i-1)*mileage x p i; let Z:=(k+1:ℕ); let q:= (Z:ℝ)⁻¹
   have hq:0<q:=inv_pos.mpr (by unfold Z; positivity)
   have h (j:ℕ)(t:ℝ)(w u:ℝ)(hh:t+(Sienna.vow*hero j+ε₀)<u): ∀ᶠ x:ℝ in atTop, w*x^t*mileage x p j≤ q*x^u:= by
       let b:= Sienna.vow*hero j+ε₀; let s:= t+b; let c:=Real.exp (p.supportExponent*81); let D:=t+b-u; have hx: ∀ᶠ x:ℝ in atTop, ((w*c) * x^D) ≤ q:= by
          have he : Tendsto (fun x:ℝ=>x^D) atTop (𝓝 0):=by simpa only [neg_neg] using tendsto_rpow_neg_atTop (by unfold D b; linarith : 0< -D)
          apply (he.const_mul (w*c)).eventually_le_const; linarith only [hq]
       filter_upwards [hx,eventually_gt_atTop (0:ℝ)] with x ht hv; let B':=Real.rpow; unfold mileage; change _*_* (c*x^b) ≤ _; rw [mul_mul_mul_comm,← Real.rpow_add hv]; unfold D at ht; rw [Real.rpow_sub hv,← mul_div_assoc] at ht; exact (div_le_iff₀ (Real.rpow_pos_of_pos hv u)).1 ht
   have he i: tint i +(Sienna.vow*hero i+ ε₀) < ε':= by linarith only [hero_earn i]
   filter_upwards [eventually_gt_atTop (0:ℝ), (eventually_all_finset a).mpr (fun i _=> (h i _ (ect c C i) _ (he i)).and (h i (tint i-1) (broker i c) θ (by linarith only [he i])))] with x hx h p' B T F hB hM d v j hU u hu w hw
   have hv i (hi:i∈a):= tavern (n:=p') x hB hM (hU i (by have hx:= mem_range.mp hi; omega))
   let Q(i:ℕ):= Buyer.book (f:=p') k B F p.clip T i; let X:ℝ:= x^ε'; let Y:ℝ:= x^θ
   have hh(V:ℝ): ∑ _i∈a, q*V=V:= by rw [Finset.sum_const,nsmul_eq_mul, ← mul_assoc,show #a=Z from card_range _,mul_inv_cancel₀ (a:=(Z:ℝ)) (by unfold Z; positivity),one_mul]
   constructor
   · rw [←hh (x^ε')]; apply sum -- edit
     intro i hi; apply grow (small (hv i hi) (coef u i)); exact (mul_le_mul_of_nonneg_right (boxMeter hx hp hu.1 hu.2 i) (by unfold mileage; positivity)).trans (h i hi).1
   have hu': integrated (n:=p') B F p.clip T k u-integrated B F p.clip T k w=∑ i∈a,(coef u i-coef w i) • Q i:= by unfold integrated; simp_rw [← sum_sub_distrib,sub_smul]; rfl
   rw [hu',←hh (|u-w| *x^θ)]; apply sum
   intro i hi; apply grow (small (hv i hi) (coef u i-coef w i)); apply (mul_le_mul_of_nonneg_right (barometer hx hp hu.1 hw.1 i) (by unfold mileage; positivity)).trans; rw [mul_assoc, mul_left_comm q]; exact mul_le_mul_of_nonneg_left (h i hi).2 (abs_nonneg _)
end dynamics
end YM.Contacts.Revest.Tucks

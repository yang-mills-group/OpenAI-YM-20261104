import YM.Contacts.Loom.Rudder
/-! # finite-order direct settlement.
 Fixed all-period local evidence. Width estimates independent via Loom budget. Proves transfer
 into same unique normalized stencil PT without *any* comparison estimate assumption at final.
 (aux here; production of claims by reader in steps only.) -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Contacts.Loom
open Function Set Filter Metric Lattice MeasureTheory
open Finset RG Wilson PertExtension.Series Radial Milling Capture Patch
open Lintel Lintel.Crag Tested
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge}
variable {X E V : Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
     [NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
     [MeasurableSpace E][BorelSpace E] [MeasurableSpace X][BorelSpace X] [MeasurableSpace V][BorelSpace V] {c b d:ℝ} {n k:ℕ}
variable {f : (ℝ×E) × V→ℝ}{g:ℝ × X→ℝ} -- err
namespace Radar
local notation "Ξ" =>(ℝ × E)
local notation "η" => Tested.germ
lemma value_eq {f g:ℕ→ℝ}(h : Bill (k+1) (peval f k-peval g k)) : ∀ j≤k,f j=g j := by
   induction k with
   | zero=>
     obtain ⟨u,hu,hU⟩ := h; intro j hj; simp only [Nat.le_zero] at hj; subst j; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; rw [← mul_zero u]; exact ge_of_tendsto ((tendsto_const_nhds (x:=u)).mul ((tendsto_id : Tendsto (fun i:ℝ=>i) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds)) (hU.mono fun i hi=>by simpa only [id_eq,peval,Pi.sub_apply,Zone.eval,pow_one,pow_zero,one_smul,sum_range_one, Nat.zero_add] using hi)
   | succ k ih=>
     let f₀:=peval f k; let g₀:=peval g k; let s:= f (k+1)-g (k+1); let V:(ℝ→ℝ):=fun x=> x^(k+1) * s
     have ht: (peval f (k+1)-peval g (k+1)) = f₀-g₀+V := by ext x; unfold f₀ g₀ peval Zone.eval; simp only [Pi.add_apply,Pi.sub_apply,smul_eq_mul]; rw [sum_range_succ _ (k+1),sum_range_succ _ (k+1)]; change _= _+x^(k+1)*s; unfold s; ring
     rw [ht] at h; have hp: Bill (k+1) V:= bill_mon s (k+1) le_rfl; have hk: Bill (k+1) (f₀-g₀):=bills_near (bill_add (bill_ge h (Nat.le_succ _)) (bill_neg hp)) (Eventually.of_forall fun x=> by simp);
     have hh:=ih hk; have hq:f₀=g₀:= funext fun x=> sum_congr rfl fun i hi=> congr_arg _ (hh i (Nat.le_of_lt_succ (mem_range.mp hi))) -- binder η∀ Unit
     rw [hq,sub_self,zero_add] at h; intro j hj; rcases Nat.lt_or_eq_of_le hj with hj|hj; · exact hh j (by omega)
     subst j; obtain ⟨D,hD,h⟩:=h; apply sub_eq_zero.mp; change s=0; apply norm_le_zero_iff.mp; have hv : 0=D*(0:ℝ):=by simp
     rw [hv]; refine ge_of_tendsto ((tendsto_const_nhds (x:=D)).mul ((tendsto_id : Tendsto (fun i:ℝ=>i) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds)) ((h.and eventually_pos).mono fun x hx=> ?_); apply le_of_mul_le_mul_left (a:=x^(k+1)) _ (pow_pos hx.2 _); obtain ⟨he,hx⟩:=hx; rw [show ‖V x‖= _ from norm_mul _ _, norm_pow,Real.norm_of_nonneg hx.le] at he; exact he.trans_eq (by rw [pow_succ _ (k+1)]; dsimp only [id]; ring)
lemma value (g:ℝ→ℝ)(a b:ℕ→ℝ)(h:Bill (n+1) (g-peval a n))(he:Bill (n+1) (g-peval b n)) (k:ℕ)(hk:k≤n) : a k=b k:= by apply value_eq (k:=n) _ k hk; exact (show (g-peval b n)+ -(g-peval a n)=_ from (show _= peval a n-peval b n from by abel)) ▸ (bill_add he (bill_neg h))
def beats (g:E→ℝ)(x:E)(n:ℕ):= expsum (Radial.layers g) n n x -- qual pipeline.scalar.H
lemma beats_zero (g:E→ℝ)(x:E) : beats g x 0=1:= by simp [beats,expsum,Zone.TaylorPow]
def gap (p:Ξ→ℝ)(x:Ξ):= p x - p (x.1,0)
def spectrum (μ:Measure V)(p:Ξ×V→ℝ)(x:Ξ)(j:ℕ):=∫ y, beats p (x,y) j ∂μ
lemma peval_scale (f:ℕ→ℝ)(v:ℝ): peval (fun i=> v*f i) k=fun x=> v*peval f k x:= by funext i; unfold peval Zone.eval; rw [Finset.mul_sum]; exact sum_congr rfl fun _ _=> mul_left_comm ..
lemma back (f:E→ℝ)(x:E)(k:ℕ)(hf: Radial.Stationary f) : Bill (k+1) (fun t=> Radial.projection 1 f t x - peval (fun i=> normTerm 1 f i x) k t) := by
    obtain ⟨C,h,H⟩:= Milling.evolve hf k (R:=‖x‖); exact ⟨_, h, H.mono fun t ht=> ht x (mem_closedBall_zero_iff.mpr le_rfl) ⟩
structure Alive (ν μ:Measure V)(lin:E→L[ℝ] X)(f : (ℝ×E) × V→ℝ)(g:ℝ × X→ℝ)(J:E→ℝ)(k:ℕ):Prop where
    hill (R:ℝ) : ∃ c> (0:ℝ),∃ C,Hilly f (c+c) R C
    money: ∃ D>(0:ℝ), ∃ v>(0:ℝ), (∀ x j, mural ν 1 f j ((1:ℝ),x) = D*Real.exp (-J x)* spectrum μ f (1,x) j) ∧ (∀ x:E,∀ L>0,∃ r>0,r < L ∧ ∃ Q:ℝ→Set V,(∀ᶠ t in η, MeasurableSet (Q t) ∧ disc t r⊆ Q t ∧ Q t⊆ disc t L) ∧ Bill (k+1) (fun t=> ash ν 1 f t (Q t) (1,x)- v*Radial.projection 1 g t (1, lin x))) -- L shadow err
    pricing: Radial.Stationary f ∧ Radial.Stationary g ∧ Measurable f
lemma polynomials (u:E)(v:ℝ)(L:E→L[ℝ] X) : peval (fun i=> v*normTerm 1 g i (1,L u)) k = (fun x=> v*Zone.eval (normTerm 1 g) k x ((1:ℝ),L u)) :=by rw [peval_scale]; rfl
variable {μ ν:Measure V}{L:E→L[ℝ] X}{J:E→ℝ}
    [ν.HasTemperateGrowth][IsProbabilityMeasure μ] (h:Alive ν μ L f g J k)
include h
lemma accounts : ∃ D>(0:ℝ),∀ x:E,∀ i≤k, (Real.exp (-J x))* spectrum μ f (1,x) i = D* kernel g (1,L x)*beats g (1,L x) i:= by
   obtain ⟨A,hA,B,hB,hZ,hF⟩:=h.money; refine ⟨A⁻¹*B,by positivity,fun x i hi=> ?_⟩; let u:Ξ:=(1,x); let t:ℝ×X:=(1,L x)
   obtain ⟨c,hc,d,H⟩:= h.hill ‖u‖; obtain ⟨η₀,hη,h₀⟩:= Milling.perspective ν h.pricing.1 (K:=1) contDiffAt_const measurable_const h.pricing.2.2 hc H k; obtain ⟨r,hr,hv,Q,hQ,p⟩:= hF x η₀ hη; obtain ⟨C,hC,he⟩:= h₀ r hr
   let v(i:ℕ):=mural ν 1 f i u; let w(i:ℕ):= B*normTerm 1 g i t; let F y:= ash ν 1 f y (Q y) u; have hp: Bill (k+1) (F-peval v k):= ⟨_,hC,(hQ.and he).mono fun i h=> (h.2 _ h.1.1 h.1.2.1 h.1.2.2 u (mem_closedBall_zero_iff.mpr le_rfl)).2 ⟩; let f' t':=Radial.projection 1 g t' t
   have H : v i=w i:= by
      refine value F v w hp (bills_near (bill_add (p) (bills_mul_l (bills_const B) (back g t k h.pricing.2.1))) (Eventually.of_forall fun i=>?_ )) i hi; change F i - B*f' i + B*(f' i-peval _ k i)=F i-peval _ k i; rw [show peval w k i= B*Zone.eval (normTerm 1 g) k i ((1:ℝ),L x) from congr_fun (polynomials (g:=g) x B L) i]; simp only [peval,Zone.eval,t]; ring
   unfold v w at H; rw [show u=((1:ℝ),x) from rfl,hZ,normTerm,Milling.unclad] at H; change A*Real.exp (-J x)*spectrum μ f _ _ = B* (beats g _ i*kernel g t) at H; change _= A⁻¹ * B*kernel g t*_; field_simp; linarith only [H] -- nonlinear casts `beats g t`
lemma base : ∀ x:E,J x-J 0 = jet g 2 (1,L x)-jet g 2 (1,0) := by
   obtain ⟨b,hb,H⟩:= accounts h; have he x:= H x 0 (Nat.zero_le _); simp_rw [beats_zero, spectrum, beats_zero, integral_const,probReal_univ, one_smul, mul_one, kernel] at he
   intro x; have hb y:Real.log (Real.exp (-J y))=Real.log b-jet g 2 (1,L y):= by rw [he y]; rw [Real.log_mul hb.ne' (Real.exp_pos _).ne',Real.log_exp]; ring
   simp_rw [Real.log_exp] at hb; have hq := hb 0; rw [map_zero] at hq; linarith only [hq,hb x]
lemma layers_eq (x:E)(i:ℕ)(hk:i≤ k): spectrum μ f (1,x) i = beats g (1,L x) i:= by
    obtain ⟨b,hb,H⟩:= accounts h; have he:= H x 0 (Nat.zero_le _); simp_rw [beats_zero,spectrum, beats_zero,integral_const,probReal_univ,one_smul,mul_one] at he; apply mul_left_cancel₀ (Real.exp_pos (-J x)).ne'; rw [H x i hk,he] -- syntax
omit h
private lemma climate {f:E→ℝ}(h:Radial.Stationary f)(x:E) : Aspiration (fun t=>Real.exp (Radial.higher f t x)) (beats f x) := by
    let Z:= Radial.zone (E:=E); intro n; obtain ⟨δ,C,e,hδ,hC,H⟩:= ((h.exponential zero_lt_one).fits n).cost; refine ⟨_,mul_nonneg (mul_nonneg hC (pow_nonneg (zero_le_one.trans (Z.high x)) e)) (Real.exp_pos (1*‖x‖^2)).le,?_⟩; have hz:0<Z.w x:=zero_lt_one.trans_le (Z.high x); filter_upwards [eventually_pos,eventually_top (show 0< δ/(Z.w x) by positivity)] with t ht hv; exact H x t ht ((le_div_iff₀ hz).mp hv.le)
private def homeBase (x:ℝ × X) : ℝ × X :=(x.1,0)
lemma paygap (hg:AnalyticAt ℝ g 0)(hf:Radial.Stationary g) (x:X): branch (beats g (1,0)) (beats (gap g) (1,x))= beats g (1,x):= by
    let v: (ℝ×X)→L[ℝ](ℝ×X) := (ContinuousLinearMap.fst ℝ ℝ X).prod 0; let f:=g∘v; have hx:AnalyticAt ℝ f 0:= Forge.starts g hg v; have hL:(gap g)=g-f:=rfl
    have hp x: jet f 1 x=0:= by erw [Garf.woven hg v x 1]; exact hf.base1 _
    have hz:Radial.Stationary (gap g):= by rw [hL]; refine ⟨(hg.sub hx).contDiffAt, sub_self _, fun u=>?_⟩; rw [Milling.Ion.jet_minus _ _ _ _ hg hx,hf.base1,hp,sub_zero]
    let h₀(t:ℝ):=Real.exp (higher g t (1,0)); let h₁(t:ℝ):= Real.exp (higher (gap g) t (1,x)); have he: Aspiration (h₀*h₁) (Tested.conv (beats g (1,0)) (beats (gap g) (1,x))):= (climate hf _).prod (climate hz _)
    have hw:(h₀*h₁)=fun t=> Real.exp (higher g t (1,x)):= by
       ext t; rw [Pi.mul_apply]; unfold h₀ h₁; rw [hL,← Real.exp_add]; unfold higher; change _= _; rw [Ion.jet_minus _ _ _ _ hg hx,Pi.sub_apply]; erw [Garf.woven (F:=g) hg v (1,x) 2]; congr 1
       simp only [f,v,Function.comp_apply,_root_.map_smul, ContinuousLinearMap.prod_apply, show ContinuousLinearMap.fst ℝ ℝ X ((1:ℝ),x)=1 from rfl,_root_.zero_apply]; ring
    rw [hw] at he; have h:= he.unique (climate hf _); rw [← h]; unfold Tested.conv Tested.term branch; ext k; simp [PowerSeries.coeff_mul]
include h
lemma transmission (hh:AnalyticAt ℝ g 0)(u:E)(i:ℕ)(hi:i≤k) : spectrum μ f (1,u) i= branch (spectrum μ f (1,0)) (beats (gap g) (1,L u)) i:= by
   rw [layers_eq h u i hi, ← paygap hh h.pricing.2.1 (L u)]; unfold branch; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [layers_eq h _ _ (by have hx:= HasAntidiagonal.mem_antidiagonal.mp hj; omega),map_zero]
end Radar
end YM.Contacts.Loom

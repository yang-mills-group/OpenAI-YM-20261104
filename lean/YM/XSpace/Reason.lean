import YM.XSpace.Inbox

/-!
# Triangular weights of radial localization
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Bracket
open Function Set Filter Lows Scale Mu Uptown Normalize Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal Contraction Finsupp
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{H:Source.Hol G}{d n k:ℕ}

private lemma waits (h:n≤k)(x:ℂ) : Tendsto (fun i:ℝ=> (i:ℂ)⁻¹^n*((i:ℂ)^k*x)) (𝓝[>] 0) (𝓝 (if k=n then x else 0)):=by
  have he:=((Complex.continuous_ofReal.tendsto 0|>.mono_left (nhdsWithin_le_nhds (s:=Ioi 0))).pow (k-n)).mul_const x
  have hs:(↑(0:ℝ):ℂ)^(k-n)*x=if k=n then x else 0:= by split_ifs with h; simp [h]; simp [Nat.sub_ne_zero_of_lt (?_ : n<k)]; omega
  rw [hs] at he; refine he.congr' ?_; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ))] with i hi; have ht:(i:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hi); rw [show (i:ℂ)^k=(i:ℂ)^n*(i:ℂ)^(k-n) by rw [← pow_add]; congr 1; omega,inv_pow]; field_simp

variable (σ:Survey G H n) (S:TaylorTower G)
lemma matters (k: Labels.Key G) (d:ℕ) (ha:Labels.generation k ≤ d+1) (h:Labels.generation k≤n):
    Tendsto (fun t:ℝ=> (t:ℂ)⁻¹^(Labels.generation k)* view (orchestra d t (seat d S)) (overture d (Encore.reel σ 0 (MvPolynomial.X k)))) (𝓝[>] 0)
        (𝓝 (probe S (reduceEq (X k)))):=by
  let n':=k.1+1; let m:Fin (d+1):= ⟨n',by unfold Labels.generation at ha; omega⟩; let L:=Trace.ping σ k; rw [reel_x]; change Tendsto (fun t:ℝ=> (t:ℂ)⁻¹^(Labels.generation k)* view _ (overture d (Trace.harp L))) _ _; simp_rw [music_at,Drama.scenic_break,Trace.leg_test,map_sum,map_smul, Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul, Complex.ofReal_pow, Finset.mul_sum]; let f (i:Fin (d+1)) (t:ℝ):ℂ:= (t:ℂ)⁻¹^(Labels.generation k) * ((t:ℂ)^(1+i.val) * ↑(Trace.probe L (release (seat d S i).val)))
  have he i:Tendsto (f i) (𝓝[>] 0) (𝓝 (if i=m then probe S (reduceEq (MvPolynomial.X k)) else 0)):=by
    by_cases hx:i=m
    · subst i; have hn: Trace.probe L (release (seat d S m).val)=(Labels.axes G k.1).coord k.2 (gaugeJet (S k.1)):=by rw [Trace.toll_due σ k (seat d S m) h,show ink (seat d S m)=S k.1 from inks _]
      unfold f; rw [hn,jet_value]; -- fix
      rw [if_pos rfl, show Labels.generation k=1+m.val from by unfold Labels.generation; show _=1+(k.1+1);omega]; simpa [Labels.read,Labels.coord] using waits (le_refl (1+m.val)) (↑((Labels.axes G k.1).coord k.2 (gaugeJet (S k.1))):ℂ)
    rw [if_neg hx]; rcases lt_or_gt_of_ne hx with g|g
    · unfold f; rw [Trace.caned_early (Trace.allows σ k) (?_ : i.val< k.1+1) (seat d S i).val]; simp [tendsto_const_nhds]; exact g
    have hi : Labels.generation k ≠1+i.val:=by have he: k.1+1< i.val :=g; unfold Labels.generation; omega
    have hp:Labels.generation k ≤1+i.val:=by have he:k.1+1< i.val:=g;unfold Labels.generation; omega
    have hh:= waits hp (↑(Trace.probe L (release (seat d S i).val)):ℂ); rw [if_neg hi.symm] at hh; exact hh
  have hf:= tendsto_finsetSum (f:=f) Finset.univ fun i _=> he i; simpa only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte] using hf
lemma power_prime (a:Labels.Key G→₀ℕ)(c:ℂ)(d:ℕ) (h:n≤d) (hp: Finsupp.weight Labels.generation a≤ n):
    Tendsto (fun t:ℝ=> (t:ℂ)⁻¹^(Finsupp.weight Labels.generation a)* view (orchestra d t (seat d S)) (overture d (Encore.reel σ 0 (monomial a c)))) (𝓝[>] 0) (𝓝 (probe S (reduceEq (monomial a c)))):=by
  classical
  revert hp; apply Extra.FD.per_factor a
  · intro h; change Tendsto _ _ _; simp [Encore.reel, overture,view,reduceEq, probe]
  intro w i hx H; rw [map_add, Finsupp.weight_single,one_smul] at H; rw [monomial_add_single,pow_one]; simp_rw [map_mul,map_add,Finsupp.weight_single,one_smul, pow_add];
  have ht:= (hx (by omega)).mul (matters σ S i d (by omega) (by omega)); exact ht.congr (fun t=> mul_mul_mul_comm ..)
lemma crystal {v:Labels.Pol G}(hv:IsWeightedHomogeneous Labels.generation v k)(hp:k≤n)(h:n≤ d):
    trunc scaleW k (archive d (overture d (Encore.reel σ 0 v)))=reduceEq v:=by
  classical
  apply resurrect; intro S; rw [v.as_sum]; simp_rw [_root_.map_sum,Finset.mul_sum]; apply tendsto_finsetSum; intro i hi; have he:=hv (MvPolynomial.mem_support_iff.mp hi); rw [← he]; exact power_prime σ S i _ d h (he.le.trans hp)

def stageCost (h:n≤ d)(p:On.Grade G n): WickPol G:= archive d (trunc coin d (overture d (Encore.reel σ 0 (Price.preparedL p).val)))
lemma pure_stage (h:n≤ d)(p:On.Grade G n): trunc scaleW n (stageCost σ h p)=p.val:=by
  rw [stageCost,← cutback, show ∀ x: WickPol G,trunc scaleW n (trunc scaleW d x)=trunc scaleW n x from ?_, crystal σ (Price.natural p) le_rfl h, Price.preparedV,On.lift_recover]
  intro x; ext i; simp_rw [trunc_ap]; split_ifs <;> first | omega|rfl

lemma steps_back (B:Hat G d){p:Stamp G}(hp:p∈OnStage G k):Chart2.pit (scenic d (radial G d B)) p=Chart2.pit (scenic d B) p:=by
  induction hp using Submodule.span_induction with
  | mem p hx=>
    obtain ⟨u,H,rfl⟩:=hx; have hh:=H.2; clear H; induction u with
    | nil=> simp
    | cons i p ih=> 
      rw [read_word,map_mul,map_mul,ih (fun i hi=> hh i (by simp [hi])),Trace.leg_test,Trace.leg_test]; congr 1
      have he := hh i (by simp); change Trace.Stops i.line at he; let v:=Trace.probe i.line; apply congr_arg ((↑):ℝ→ℂ); unfold scenic castBlaze; simp_rw [LinearMap.comp_apply,LinearMap.sum_apply,map_sum]; refine Finset.sum_congr rfl fun j _=>?_; change v (release (assay _ (B j)).val)= v (release (B j).val); obtain ⟨z,hz⟩:=assayed (B j); conv_rhs => arg 2; arg 2; arg 1; rw [hz]; skip
      rw [Submodule.coe_add,map_add,map_add, show release (Scale.pipes z).val= _ from Scale.blown z, show v (Scale.stream _) = 0 from he _,add_zero]
  | zero=>simp
  | add=> simp_all only [map_add]
  | smul=> simp_all only [map_smul]
end YM.XSpace.Bracket

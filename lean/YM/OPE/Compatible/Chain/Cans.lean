import YM.OPE.Compatible.Chain.Badges
/-!
# leading positivity I. Relative any caps at fixed launch; higher legs unclaimed
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06 Work.F08
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
lemma upperWind (C:KernelChoices)(h:4 ≤ r):∃ B>0,∀ v:Train r,∀ n:Side,∀ x:form 1 n, x ⬝ᵥ(major (ShellRow C v) n*ᵥx) ≤ B*(x ⬝ᵥx):=by
     let F:= fun u:Train r => pink C.penalty u; let P:= (heart_heats C.penalty C.penalty_pos h (fun i:Train r=> i)).1.stock; let D:= cobound 1; let T: Row M M:= composeRows (cobound 0) (transRows (cobound 0)); have hT:Whole T:= (Whole.boundary 0).prod (Whole.boundary 0).flipped
     let K:=fun v:Train r=>minusRows (ShellRow C v) (scaleRows (-1) T); have hX:Stock (α:=fun _=>M) (β:=fun _=> M) (fun _=>1) K:=by
       have hp:Stock (α:=fun _ :Train r=> M) (β:=fun _=>TypeFace 2) (fun _=>1) (fun _=> transRows D):=Stock.constant _ (Whole.boundary 1).flipped; have hs := hp.times P; simp_rw [one_mul] at hs
       have ht:= hs.times (Stock.constant (ι:=Train r) D (Whole.boundary 1)); simp_rw [one_mul] at ht; exact ht.minus (Stock.constant _ (hT.weight _))
     obtain ⟨s,U,hs,hu,H⟩:=hX.uniform; simp only [mul_one] at H; let t:ℝ:=Fintype.card M; have hQ:0<t:=by unfold t; have he : Nonempty M:=⟨Exterior.coord 0⟩; haveI := he; positivity
     refine ⟨_,mul_pos hQ hu,fun v n x=>?_⟩; rw [show major (ShellRow C v) n=(K v).acts n from ?_]; apply (le_abs_self _).trans (schur_qf _ _ (taxi_schur (strip_mono (H v) hs.le le_rfl) le_rfl n) x)
     unfold K; rw [(Op_whole h v (C:=C)).less (hT.weight _),acts_scale]; unfold T; rw [(Whole.boundary _).acts (Whole.boundary _).flipped,acts_trans]; change _ = _- -1 • (grad n*(grad n)ᵀ); simp [major]
variable (H:Even n.val)
local notation "TK" => Libra.Keys G (Limb H)
abbrev PressX (x:TK):ℝ:= ∑ i:Limb H,‖x i‖^2
private lemma painted (x:TK): PressX H x* (4:ℝ)=∑ i:G.ColorIndex, parts G 1 (cloak H x) i ⬝ᵥ parts G 1 (cloak H x) i:=by
      let f(v:edgeV n):= ‖hover H x v‖^2
      have he: (∑ i,f i)= 4 • ∑ i:Limb H, f i.val:=by
           have h(i k): f ((edgesK H).go k i)= f i:=by
                  unfold f; rw [hoverEll H x k i]; split; rw [norm_neg]; rfl; rfl
           convert! (edgesK H).sumRep f h using 1; congr!
      rw [← show ∑ j:Limb H, f j.val= PressX H x from sum_congr rfl (fun i _=>by unfold f; rw [hover_reap])]; -- type mismatch sums
      calc
           _=∑ i,f i:=by rw [he]; simp [nsmul_eq_mul,mul_comm] -- issue
           _=_:=by unfold dotProduct; rw [Finset.sum_comm,← Equiv.sum_comp addressR]; apply Finset.sum_congr rfl; intro i _; let v:=hover H x i; have he: cloak H x (addressR i)=v:= by change cloak H x (i.1,Exterior.coord i.2)=_; rw [cloak_at]
                   change ‖v‖^2 = _; unfold parts; simp only [he]; rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]; simp [pow_two]
lemma boostUpper (h:4≤r) : ∃ B:ℝ, 0<B ∧ ∀ v:Train r,∀ (n:Side)(H:Even n.val),∀ x: Keys G (Limb H), (boost H v h C).P x x ≤ B* PressX H x:=by
      obtain ⟨b,hb,H⟩:= upperWind C h; refine ⟨b,hb,fun v n ht x=> ?_⟩; rw [boost_price, flag]; rw [div_le_iff₀ (show (0:ℝ)<4 by norm_num),mul_assoc,painted, Finset.mul_sum]; exact sum_le_sum (fun j _=> H v n _)
end YM.OPE.Cascade.Terp

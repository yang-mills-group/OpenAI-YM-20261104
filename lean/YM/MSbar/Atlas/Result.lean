import YM.MSbar.Atlas.Noon
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
variable (P:Patch)(K:KernelChoices)(J:Voice G) (A B:Stage)(p:Palisade)
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
-- Vacuum concentration, rates uniform in angular frame, link positions and both periods.Presentation-preserving.
def pluma {c f:Side}{S:StepData c f}(J:Voice G)(R:Rep G f)(V:Positions (Primary c G))(t:S.Choices)(F: Forest S.ratio)(j:Key F G)(a:ℝ):Set (Config G f) :={U | a < |fareX F J (represent (tint G _ V)) U j.1 j.2 - vest (priced F t R.clip R.path) V j|}
structure Horizon (P : Patch)(K:KernelChoices)(G:Gauge)(J:Voice G)(A B:Stage) (p:Palisade) (n:ℕ) (s₀:ℝ) (d:ℝ):Prop where
   gains : ∀ {c f:Side}{S:StepData c f} (R:Rep G f)(Y:Rep G c), S.patch=P → S.kernel=K → Season J A B s₀ R Y S (courage G P.L s₀)→
      ∀ (F:Forest S.ratio) (j:S.Choices) (t:Key F G)(V:Positions (Primary c G)), Grants j R F p n → ‖V‖ ≤ skies (tip G P.L s₀) →
         let x := tip G P.L s₀
         chance S R (represent (tint G _ V)) (pluma J R V j F t (3*distance x)) ≤ x^d
lemma ever (g:Clear G J)(n:ℕ)(d:ℝ): ∀ᶠ x:ℝ in atTop,Horizon P K G J A B p n x d:=by
    have hd:= (snowbank P G).mul (odometer P p G)
    let e(x:ℝ):=digits G p (Ξ x); let v(x:ℝ):= Real.exp (rpay (Ξ x)*e x)+snow G P x* ↑(digits G p (Ξ x))
    have hv : Pole G L v:= (endLap P p G).add hd
    by_cases he: 0 < p.gap ∧ 0<p.a ∧ 0<p.density
    · filter_upwards [solders P K J A B p g he.1 he.2.1 he.2.2, shiftedLog G P.L, (hv (d-1)|>.mul_left 2) d (by linarith)] with x hx hb hm -- shift typo
      constructor
      intro c f S R Y he ht h F j i V hp hV l
      have hB:= h.case_; rw [he] at hB
      let pB:= snow G P x -- typo
      let iB:= courage G L x
      have hF(t') (hθ:|t'|=increments l):= Tinted.business P K J A B p j F i x V he ht h (hx R Y hB h.hull) hp g (Real.exp_pos _|>.le) (Real.exp_pos _|>.le) t' hV hθ
      have he' :0<l:=zero_lt_one.trans hB.enough; let t':= increments l; let d0:=distance l
      have ht':0<t':= Real.rpow_pos_of_pos he' _; let Ax:=tailsSet F J j i t' V R (3*(increments l*distance l)); let Bx:=tailsSet F J j i (-t') V R (3*(increments l*distance l)); let W:=represent (tint G _ V)
      have he(P:ℝ):MeasurableSet (tailsSet F J j i P V R (3*(increments l*distance l))):=(fees F J j i P (radiusB l) V g _ (k:=0)).from_here -- m.W. order
      have hd:pluma J R V j F i (3*d0) = Ax∪Bx:=by
          ext x'; let y:=fareX F J W x' i.1 i.2- vest (priced F j R.clip R.path) V i
          change 3*d0 < |y| ↔ 3*(t'*d0)<t'*y ∨ 3*(t'*d0)< -t'*y
          rw [lt_abs]; constructor
          · intro p; rcases p with P|P; left; linarith only [mul_lt_mul_of_pos_left P ht']; right; linarith only [mul_lt_mul_of_pos_left P ht']
          intro P; rcases P with P|P; left; nlinarith only [P,ht']; right; nlinarith only [P,ht'] -- contrapositive
      rw [hd]; have hA:Admitted W R S B.width B.paths (ability l) (lbt l) 1:=by
          have hh: R.eval≠0:=by intro he; have hp:=h.shine 1; rw [he] at hp; change 0<(0:ℝ) at hp; linarith
          refine ⟨hB.lawful,fun U=> h.shine _|>.le,?_ ,S.isKernel h.bends.1 _⟩
          apply SectorNext.Vacuum.push_pos S h.bends.1 R.beta R.eval ((R.envelope hB.lawful).integrable _) (fun _=> h.shine _|>.le) _ W
          apply (integral_pos_iff_support_of_nonneg (fun _=>h.shine _|>.le) ((R.envelope hB.lawful).integrable (prior G f))).2
          rw [show Function.support R.eval=Set.univ from Set.eq_univ_of_forall fun i=> (h.shine _).ne']; simp

      have hgX := (union_bound hA (he t') (he (-t'))).trans (add_le_add (hF t' (abs_of_pos ht')) (hF (-t') (by rw [abs_neg,abs_of_pos ht'])))
      refine hgX.trans ((le_of_eq (show _+_=2*v x from ?_)).trans ((le_abs_self _).trans hm)); unfold v e; ring
    exact Eventually.of_forall fun x=> ⟨fun _ _ _ _ _ _ _ _ _ hk _=> (he ⟨hk.buys.pos_m,hk.buys.pos_a,hk.buys.pos_C⟩).elim⟩
lemma armlet (h:P.Branches K G)(b:Clear G J) (n:ℕ)(hn:3≤n): ∃ p:Palisade, (∀ d, ∀ᶠ x in atTop, Horizon P K G J A B p n x d) ∧ ∀ {c f:Side}{S:StepData c f} (R:Rep G f)(Y:Rep G c)(x:ℝ), S.patch=P → S.kernel=K → Season J A B x R Y S (courage G P.L x)→
      ∀ (F:Forest S.ratio)(t:S.Choices), Grants t R F p n:=by
    obtain ⟨a,ha⟩:= tickets P K G B.clip B.width_pos B.paths hn h
    refine ⟨a,ever P K J A B a b n,fun R Y x h H hx F t=>ha h H F t _ R (hx.case_ |>.clip) ((hx.case_|>.clip) ▸ hx.case_.lawful.paths) hx.bends⟩
end YM.MSbar.Heath.Stock

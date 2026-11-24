import YM.Integration.WilsonOriginalNullPlacedParallel
import YM.Integration.WilsonOriginalNullFactoryRoute

/-! Center each emitted calibrated section at its true parent, keeping
its actual remaining kernel history. The two residual accounts stay
on their original Wilson densities. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedHistory
open Function Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (d N p b:ℕ) (W:∀ j,Rep G (R.family.side j p))
    (o:∀ j,Site (R.family.side j p)) {ε:ℝ}
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d
local notation "P₀" j:max => (C₀).path.rep N p j
local notation "κ" j:max => safety C₀ j
local notation "Φ" j:max x:max => ((calValues (C:=C₀) d N p (b+j) x) ∘ Lattice.translate (o (b+j)))
local notation "ordinary" j:max v:max => Coefficient.density v (o (b+j)) S₀ (W (b+j))
local notation "physical" j:max v:max => Coefficient.density v (o (b+j)) S₀ (P₀ (b+j))

theorem finite (ep:0 ≤ ε) : ∀ n:ℕ, b+n ≤ N →
    (∀ j<n, o (b+j) = ((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))) →
    (∀ j<n, ∃ a c f t s:ℝ,(W (b+j)).Lawful a c f t s) →
    (∀ j<n,Opened C₀ d (b+j) p) →
    (∀ j<n,WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε) →
    ∀ (h k:Coefficient F₀ ((C₀).side (b+n) p)) (B D:ℝ),
      h.Format (o (b+n)) (C₀).params (W (b+n)) → h.remBound (o (b+n)) (W (b+n)) (κ (b+n)) B →
      projection F₀ (C₀).params (W (b+n)).p.threshold (o (b+n)) h=0 →
      k.Format (o (b+n)) (C₀).params (P₀ (b+n)) → k.remBound (o (b+n)) (P₀ (b+n)) (κ (b+n)) D →
      projection F₀ (C₀).params (P₀ (b+n)).p.threshold (o (b+n)) k=0 →
      ∃ (v w:Coefficient F₀ ((C₀).side b p)) (x:ℕ→(C₀).label d) (u e:ℝ),
        v.Format (o b) (C₀).params (W b) ∧ v.remBound (o b) (W b) (κ b) u ∧
        projection F₀ (C₀).params (W b).p.threshold (o b) v=0 ∧
        w.Format (o b) (C₀).params (P₀ b) ∧ w.remBound (o b) (P₀ b) (κ b) e ∧
        projection F₀ (C₀).params (P₀ b).p.threshold (o b) w=0 ∧
        u+e ≤ gain C₀ b (b+n)*(B+D) ∧
        (∀ j<n,mCost C₀ d N p (b+j) (x j) ≤ ε*gain C₀ (b+j) (b+n)*(B+D)) ∧
        flow C₀ d N p b n (ordinary n h+physical n k) =
          v.density (o b) S₀ (W b)+w.density (o b) S₀ (P₀ b) +
          ∑ j∈Finset.range n,flow C₀ d N p b j (Φ j (x j)) := by
  intro n
  induction n with
  | zero =>
    intro hn route laws home gates h k B D hf hp hz kf kp kz
    exact ⟨h,k,fun _=>0,B,D,hf,hp,hz,kf,kp,kz,by simp [gain_self],by simp,by simp [flow]⟩
  | succ n ih =>
    intro live route laws home gates h k B D hf hp hz kf kp kz
    have last:=Nat.lt_succ_self n
    obtain ⟨s,t,j,u,e,sf,sp,sz,tf,tp,tz,sum,fee,heard⟩:=gates n last h k B D hf hp hz kf kp kz
    rw [←route n last] at sf sp sz tf tp tz heard
    obtain ⟨v,w,x,c,f,vf,vp,vn,wf,wp,wn,small,price,full⟩:=ih (by omega)
      (fun j hj=>route j (by omega)) (fun j hj=>laws j (by omega)) (fun j hj=>home j (by omega))
      (fun j hj=>gates j (by omega)) s t u e sf sp sz tf tp tz
    let L:=factor C₀ (b+n)
    let δ:=L^(-rate)
    have lp:0<L:=zero_lt_one.trans (factor_positive C₀ (b+n))
    let emitted:ℕ→(C₀).label d:=fun j' => if j'=n then j else x j'
    refine ⟨v,w,emitted,c,f,vf,vp,vn,wf,wp,wn,?_,?_,?_⟩
    · have h:=small.trans (mul_le_mul_of_nonneg_left sum (Real.exp_pos _).le)
      rw [show b+(n+1)=b+n+1 by omega,gain_step]
      exact h.trans_eq (by ring)
    · intro y hy;rcases lt_or_eq_of_le (Nat.le_of_lt_succ hy) with earlier|atTopDate
      · rw [show emitted y=x y from if_neg (Nat.ne_of_lt earlier),show b+(n+1)=b+n+1 by omega,gain_step]
        have h:=(price y earlier).trans (mul_le_mul_of_nonneg_left sum (mul_nonneg ep (Real.exp_pos _).le))
        exact h.trans_eq (by ring)
      · subst y
        rw [show emitted n=j from if_pos rfl,show b+(n+1)=b+n+1 by omega,gain_step,gain_self,one_mul]
        calc
          _ = L^(-rate)*(L^rate*mCost C₀ d N p (b+n) j) := by rw [←mul_assoc,←Real.rpow_add lp,neg_add_cancel,Real.rpow_zero,one_mul]
          _ ≤ L^(-rate)*(ε*(B+D)) := mul_le_mul_of_nonneg_left fee (Real.rpow_nonneg lp.le _)
          _ = _ := by ring
    · obtain ⟨_,_,_,_,_,law⟩:=laws n last
      have plaw:=(R.makes.wilson.represents N p (b+n) (by omega)).good
      have inside:Integrable (ordinary n s+physical n t) (prior G _):=
        ((s.envelope S₀ law sp sf).integrableC _).add ((t.envelope S₀ plaw tp tf).integrableC _)
      obtain ⟨af,ap,_,av⟩:=WilsonOriginalNullFactoryRoute.entrance R d (N:=N) (p:=p)
        (show b+n ≤ N by omega) (home n last) (o (b+n)) j
      let qa:=Drift.stamp (o (b+n)) (Tour.placard C₀ R.makes N p (show b+n ≤ N by omega) (o (b+n)))
        (((C₀).factory d N p).entries (b+n) j)
      have av':qa.density (o (b+n)) S₀ (P₀ (b+n)) = Φ n j:=av
      have outside:Integrable (Φ n j) (prior G _):=by rw [←av'];exact (qa.envelope S₀ plaw ap af).integrableC _
      have lower:(∑ y∈Finset.range n,flow C₀ d N p b y (Φ y (emitted y))) =
          ∑ y∈Finset.range n,flow C₀ d N p b y (Φ y (x y)):=by
        apply Finset.sum_congr rfl;intro y hy
        rw [show emitted y=x y from if_neg (Nat.ne_of_lt (Finset.mem_range.mp hy))]
      rw [show flow C₀ d N p b (n+1) (ordinary (n+1) h+physical (n+1) k) =
        flow C₀ d N p b n ((ordinary n s+physical n t)+(Φ n j)) from congrArg (flow C₀ d N p b n) heard,
        flow_add C₀ d N p b n _ _ inside outside,full,Finset.sum_range_succ,lower,show emitted n=j from if_pos rfl]
      abel

end YM.Integration.WilsonOriginalNullPlacedHistory

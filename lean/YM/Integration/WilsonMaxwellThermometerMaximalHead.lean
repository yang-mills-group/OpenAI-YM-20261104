import YM.Integration.WilsonPositionThermometerCapStation

/-! The signed maximal-rank coordinate of a true positioned Wilson cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerMaximalHead
open Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Next.Rank.Atlas Further.CorrectedLift
open Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open scoped BigOperators Classical Topology
variable {G : Gauge} {d : ℕ}

theorem rank (F:Labels.Frame G d) (i:F.Index) : (F.grades i).2≤d/2 := by
  suffices 2*(F.grades i).2≤d by omega
  let v:=F.basis i
  have h:v.val≠0:=fun e=>(Module.Basis.ne_zero F.basis i) (Subtype.ext e)
  obtain ⟨l,hL⟩:v.val.support.Nonempty:=Finset.nonempty_iff_ne_empty.mpr (fun e=>h (MvPolynomial.support_eq_empty.mp e))
  have hgrade : Finsupp.weight bidegree l=F.grades i :=
    (pure_grade _ v).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hL)
  apply le_trans _ (F.bound i)
  rw [←hgrade,weight_slot]
  unfold height
  rw [Finsupp.weight_apply]
  unfold Finsupp.sum
  simp only [Finset.mul_sum]
  exact sum_le_sum fun j _=>by
    change 2*l j≤l j*generation j
    rw [mul_comm 2]
    exact Nat.mul_le_mul_left _ (show 2≤generation j from Nat.le_add_left _ _)

def error (F:Labels.Frame G d) (χ:ℝ) (x p:F.Coeff) : ℝ :=
  ∑ i:F.Index, if F.grades i=(d,d/2) then ‖(χ:ℂ)*x i-p i‖ else 0

theorem block (F:Labels.Frame G d) (ρ θ ε:ℝ) (x y p:F.Coeff)
    (scale:1≤ρ) (pos:0<θ) (small:θ≤1) (payment:0≤ε) (half:ε<1)
    (eqn:∀ i:F.Index,(θ:ℂ)^(F.grades i).2*y i=(ρ:ℂ)^(F.grades i).1*p i)
    (rent:F.coeffSize (x-y)≤ε*F.coeffSize x) :
    error F (θ^(d/2)/ρ^d) x p ≤ ε/(1-ε)*F.coeffSize p := by
  let χ:=θ^(d/2)/ρ^d
  have rpos:0<ρ:=zero_lt_one.trans_le scale
  have dome:0<ρ^d:=pow_pos rpos _
  have hχ:0≤χ:=div_nonneg (pow_nonneg pos.le _) dome.le
  have allowance:χ*F.coeffSize y≤F.coeffSize p:=by
    change θ^(d/2)/ρ^d*(∑i,‖y i‖)≤∑i,‖p i‖
    rw [div_mul_eq_mul_div,div_le_iff₀ dome,mul_comm (∑i:F.Index,‖p i‖),Finset.mul_sum,Finset.mul_sum]
    apply sum_le_sum;intro i _
    have mode:=congrArg norm (eqn i)
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos,abs_of_pos rpos] at mode
    calc θ^(d/2)*‖y i‖ ≤ θ^(F.grades i).2*‖y i‖ :=
           mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one pos.le small (rank F i)) (norm_nonneg _)
         _ = ρ^(F.grades i).1*‖p i‖ := mode
         _ ≤ ρ^d*‖p i‖ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ scale (F.bound i)) (norm_nonneg _)
  have tri:F.coeffSize x ≤ F.coeffSize (x-y)+F.coeffSize y:=by
    unfold Frame.coeffSize;rw [←sum_add_distrib];apply sum_le_sum; intro i _
    simpa only [Pi.sub_apply,sub_add_cancel] using (norm_add_le (x i-y i) (y i))
  have paid : χ*F.coeffSize (x-y)≤ε/(1-ε)*F.coeffSize p:=by
    have h1:=mul_le_mul_of_nonneg_left rent hχ
    have h2:=mul_le_mul_of_nonneg_left tri hχ
    have h3:χ*F.coeffSize x ≤χ*F.coeffSize (x-y)+F.coeffSize p :=by
      rw [mul_add] at h2;exact h2.trans (add_le_add_right allowance _)
    have h4:=mul_le_mul_of_nonneg_left h3 payment
    rw [show ε/(1-ε)*F.coeffSize p = (ε*F.coeffSize p)/(1-ε) by ring,le_div_iff₀ (sub_pos.mpr half)]
    nlinarith only [h1,h4]
  apply le_trans _ paid
  change (∑i:F.Index, if F.grades i=(d,d/2) then _ else 0)≤χ*(∑i,‖(x-y) i‖)
  rw [Finset.mul_sum]
  apply sum_le_sum;intro i _
  by_cases hi:F.grades i=(d,d/2)
  · have mode:=eqn i
    rw [hi] at mode
    have hθ:(χ:ℂ)*y i=p i:=by
      change ((θ^(d/2)/ρ^d:ℝ):ℂ)*y i=p i
      push_cast
      rw [div_mul_eq_mul_div,div_eq_iff (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr rpos.ne')),mode,mul_comm]
    rw [if_pos hi]
    change ‖(χ:ℂ)*x i-p i‖ ≤ χ*‖x i-y i‖
    rw [←hθ,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hχ]
  · rw [if_neg hi]; exact mul_nonneg hχ (norm_nonneg _)

variable {C:Family G} {f:Extraction.Order} {H:(Bel C.book).Hierarchy}

theorem stationed (h:C.Makes) {D:ℕ} (V:Vane C D) (funded:V.checked f H D)
    (j:Fin (D+1)) (w:(Bel C.book).Field j) (N per:ℕ) (top:V.k<N)
    (scale:1≤Station.mag C.path.levels V.b V.k) (small:shrink C V.k N per≤1)
    (half:Perch.bill (-1/2) (clim C.path.levels V.k)<1) :
    let θ:=shrink C V.k N per
    let ρ:=Station.mag C.path.levels V.b V.k
    let p:=ladder C j w
    let v:=V.wheel.atCut (N,per) j w
    let ε:=Perch.bill (-1/2) (clim C.path.levels V.k)
    error (C.labels.level j) (θ^(j.val/2)/ρ^j.val) (awake C j V.k N per v) p ≤
      ε/(1-ε)*(C.labels.level j).coeffSize p := by
  intro θ ρ p v ε
  obtain ⟨charts,sky⟩:=funded.rate N per top
  have solved: Solves C ρ j V.k N per (V.R N per j) p v :=
    poured h (funded.early j) top.le ρ _ ((charts j).1) p
  apply block (C.labels.level j) ρ θ ε _ ((V.R N per j) v) _ scale (shrink_pos C h top.le per) small
    (Real.exp_pos _).le half _ (sky j v)
  intro i
  simpa only [Solves,Frame.scaled_apply,Complex.ofReal_pow,weightTag,LinearMap.coe_mk,AddHom.coe_mk]
    using congrFun solved i

end YM.Integration.WilsonMaxwellThermometerMaximalHead

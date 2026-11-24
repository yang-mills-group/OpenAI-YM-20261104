import YM.RG11Proof.Stress.Closing
/-!
# Finite Stress normalization conversion (separated arrays)

Once matched, finite horizon d=4 (apply restriction to actual nested h≥6)
& power N and stress coefficients through N. DOESN'T construct the
normalized stress/mark in WilsonX or MS and does not identify actual or
interacting Ward identities (use RG13 etc). Does *derive* transformation
of the fixed vacuum-free graded candidate from just the matched arrays and
two required linear Ward tests common to the prescriptions (e.g. via
`survey_integrated` if each supplies indicated Smooth support kernels);
on the actual leading Maxwell quotient with rank & normalization sign proved,
not a premise on a Ward detector. Any extra unit term requires separate
comparison (invisible to these tests; don't silently read it at contacts).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Stress
open scoped Classical BigOperators ContDiff Topology
open YM.RG11.Fields YM.RG11.Scale YM.RG11.Jets YM.RG11.Nodes PowerSeries
open Table Maxwell Labels Function
variable {G:Gauge}{F:Frames G}(A C:ShapeReport G F)(B:Adapted F 4)

-- helper to transport T,D etc in complex rectangular component arrays
private theorem deposit_compose (p f:PowerSeries ℝ)(hp:Anchored p):
    Jets.deposit (PowerSeries.subst p f)= PowerSeries.subst (Jets.deposit p) (Jets.deposit f):=by
  ext1 k
  rw [coeff_compose _ _ _ (deposit_base p hp), Jets.deposited,coeff_compose _ _ _ hp,Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [←map_pow Jets.deposit,Jets.deposited,Jets.deposited,Complex.ofReal_mul]

private theorem lays (X Y:psStress B.toBasis)(p:Change ℝ B.toBasis.J)(hp:Anchored p.g):
     shine B.toBasis (Y*p.Z-subs p.g X)= shine B.toBasis Y*(toComplex p).Z-subs (toComplex p).g (shine B.toBasis X):=by
  ext i j k
  congr 1
  simp only [shine,toComplex, Matrix.map_apply,Matrix.sub_apply,Matrix.mul_apply,subs_apply,map_sub,map_sum,map_mul,deposit_compose _ _ hp]

private theorem cost (X: psStress B.toBasis)(k:ℕ):piece k (shine B.toBasis X)= (piece k X).map Complex.ofRealHom:=by ext i j; simp only [shine,piece_apply,Matrix.map_apply,Jets.deposited]; rfl

 theorem survives {X Y:psStress B.toBasis}{N}(p:Change ℝ B.toBasis.J)(hl:B.toBasis.guard.Lawful p.Z)(hp:Anchored p.g)(hg:∀ k≤N,graded (Fields.height B) (piece k p.Z))
     (hX:∀ i≤N,piece i X∈candidate B)(hY:∀i≤N,piece i Y∈candidate B):∀ k≤N,piece k (Y*p.Z - subs p.g X)∈candidate B:=by
   intro k hk
   have he (Z V:psStress B.toBasis):piece k (Z-V)=piece k Z-piece k V:=Matrix.ext fun i j=>by simp
   rw [he,piece_mul,piece_subs hp]; apply (candidate B).sub_mem
   · refine Submodule.sum_mem _ ?_; intro z hz; have he:= Finset.HasAntidiagonal.mem_antidiagonal.mp hz
     by_cases hs:z.2=0
     · rw [hs,hl.baseline,Matrix.mul_one]; exact hY _ (by omega)
     exact reorient B (hY _ (by omega)) (hl.positive (by omega)) (fun hm=>hg _ (by omega) hm)
   refine Submodule.sum_mem _ (fun i hi=> Submodule.smul_mem _ _ (hX i ?_)); have hu:=Finset.mem_range.mp hi; omega

 theorem lining (hG:G.Simple){χ:E4→ℝ}(hw:Window (UVNext.FreeStress.camera 0) χ)
    (p:Change ℝ B.toBasis.J)(hp:Anchored p.g)(hZ:B.toBasis.guard.Lawful p.Z){N}
    (hm:∀ v,Through N (p.act (A.realAt B.toBasis) v) (C.realAt B.toBasis v))
    (he:∀ k≤N,graded (Fields.height B) (piece k p.Z))
    {X Y:psStress B.toBasis}(hX:∀ i≤N,piece i X ∈ candidate B)(hY:∀ i≤N,piece i Y∈candidate B)
    (Hx:Signals A B.toBasis X N hw)(Hy:Signals C B.toBasis Y N hw):
    MatThrough N (Y*p.Z) (subs p.g X):=by
  let T:= Y*p.Z-subs p.g X
  let d:= toComplex p
  have hg:Anchored d.g:=deposit_base _ hp
  have hz:nearId d.Z:=by
     change piece 0 (p.Z.map Jets.deposit)=1
     have H (i j:B.toBasis.J): coeff 0 (p.Z i j)=(1:Square B.toBasis.J ℝ) i j:=congrArg (fun (D:Square B.toBasis.J ℝ)=>D i j) hZ.baseline
     ext i j
     simp only [piece_apply,Matrix.map_apply,Jets.deposited,H,Matrix.one_apply]
     split_ifs <;> simp
  have ht(k)(hk:k≤N):piece k T=0:=by
    induction k using Nat.strong_induction_on with
    | h k ih=>
    have hi i (ht:i<k): piece i (shine B.toBasis T)=0:=Matrix.ext fun a b=>by rw [cost,Matrix.map_apply, ih i ht (ht.le.trans hk)]; simp
    apply ranking A B hG hw _ (survives B p hZ hp he hX hY k hk)
    all_goals
       intro v
    · let t(i:Taps):=shellers direct i
      have hu:= (mandate_forces (d:=d) hg (fun i z=>survey_match A B.toBasis C hp hm z (t i)) (fun i=>survey_match A B.toBasis C hp hm i (n:=1) 0) Hx.diverges Hy.diverges v) k hk
      rw [← lays B X Y p hp,map_zero,curb d.Z _ hi v (by convert! hz)] at hu
      simp_rw [base_compose _ _ hg, cost B] at hu; exact hu
    let t(i:Taps):=shellers (traded hw) i
    have hu:= (mandate_forces (d:=d) hg (fun i z=>survey_match A B.toBasis C hp hm z (t i)) (fun i=>survey_match A B.toBasis C hp hm i (directional (n:=2) 0 0 (UVNext.FreeStress.shutter 0))) Hx.translates Hy.translates v) k hk
    rw [← lays B X Y p hp,map_zero,curb d.Z _ hi v (by convert! hz)] at hu
    simp_rw [base_compose _ _ hg,cost B] at hu; exact hu
  apply MatThrough.of_piece; intro i hi
  apply sub_eq_zero.mp; rw [←ht i hi]; ext z v; simp [T]
end YM.RG11.Stress

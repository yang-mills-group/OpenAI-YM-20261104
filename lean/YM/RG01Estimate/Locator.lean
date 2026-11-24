import YM.RG01Estimate.Plan
import YM.Pert.Kinetic.Ebb
/-!
 # Sharpened wrap cost of two pre-reset representations of the same kernel/output stack
 with SAME β and kinetic basis. Hessian, WITHOUT mask differentiation. Every local address
 tested separately. Use `judge` on the TOTAL genuine Hessian. Even for wrapping terms;
 those need explicit bounds, not exact identities. Crucial to reserve enough support
 for WRAPPING padding of a clover, to keep canonical-β extraction *exactly* on that path.
 This uses the verified `Affine.lean` & projection conventions, not continuum RT.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor
open Function Filter Set Finset Lattice Wilson RG AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Support n}{f:Pot G n}
    (g:G.Simple) (h:p.Regular X f)

def needle (G:Gauge)(x:Site n) : Directions G n := fun e=>if e=(x,1) then spike G else 0
def pitch (x y : Site n) : ℝ := coord y x 0
def wires (f:Pot G n) (x y: Site n) := logHessian f (needle G x) (needle G y)
def judge (f : Pot G n) : ℝ := -(1/2:ℝ)*∑ x:Site n,∑ y:Site n,pitch x y^2 * wires f x y

lemma knit (x y o : Site n) (hx:10*separation x o<n.val)(hy:10*separation y o<n.val) : pitch x y=pitch x o-pitch y o:=by
    have h : lift (x-y)=lift (x-o)-lift (y-o):= by
        refine lift_eq_iff.mpr ⟨?_,fun i=> ?_⟩
        · rw [map_sub,wrap_lift,wrap_lift]; abel
        have hg : (lift (x-o) i).natAbs ≤ separation x o:= component_le _ _
        have ht : (lift (y-o) i).natAbs ≤ separation y o:= component_le _ _
        simp only [Pi.sub_apply]; omega
    unfold pitch coord; simp [h]
lemma limited (x y : Site n) : |pitch x y| ≤ n.val:= by
    have hh:= lift_centers (x-y) 0
    unfold pitch coord
    rw [← Int.cast_abs]
    exact_mod_cast (show |lift (x-y) 0| ≤ (n.val:ℤ) by rw [abs_le]; omega)
lemma needle_field (o : Site n) : (∑ x, pitch x o • needle G x)=(wedge axes01 (spike G)).field o:= by
    funext i
    rw [Finset.sum_apply, wedge_field]
    rcases i with ⟨i,j⟩; by_cases h: (1:Axis)=j
    · subst j; rw [Finset.sum_eq_single i]
      · simp [needle,axes01,pitch]
      · intro x _ hx; simp only [Pi.smul_apply,needle,Prod.mk.injEq,and_true,if_neg (Ne.symm hx),smul_zero]
      simp
    rw [if_neg (show (axes01.val).2≠j from h)]; simp [needle,Ne.symm h]

def constant (G:Gauge) : LinearJet G := ⟨fun i=>if i=1 then spike G else 0,0⟩
lemma needles (o : Site n) : ∑ x:Site n, needle G x=(constant G).field o :=by
    funext i; rw [Finset.sum_apply]
    rcases i with ⟨i,j⟩
    by_cases h: j=1 <;> simp [needle,constant,h,LinearJet.field]

include g h
lemma quiet {o:Site n} (hx:Nonwrapping X o)(hn:4≤n.val) (a : Directions G n) : logHessian f ((constant G).field o) a=0 :=by
   apply ((constant G).hessian_curl₁ g h hx hn {at0:=0,slope:=0} (by ext1; rw [LinearJet.positive,LinearJet.curl,LinearJet.positive,LinearJet.curl]; rfl) a).trans
   rw [show (LinearJet.mk (0:Axis→G.Color) 0).field o=(0:Directions G n) by ext1; simp [LinearJet.field]]; simp [hessian_eq]
lemma absent (x y : Site n) (hw:x∉ X): wires f x y=0:= by
   have hb: Agrees (X : Set (Site n)) (needle G x) 0:= by
       intro e he _; change (if e=(x,1) then spike G else 0)=0; split
       next h=> rw [h] at he; exact (hw he).elim
       rfl
   unfold wires; rw [hessian_agrees g h hb (show Agrees ↑X (needle G y) (needle G y) from fun _ _ _=>rfl)]; simp [hessian_eq]
lemma row_zero {o:Site n} (hx:Nonwrapping X o)(hn:4≤n.val)(y:Site n) : ∑ x:Site n, wires f x y=0:=by
    have hv : ∀ z:Directions G n, logHessian f ((∑ x, needle G x):Directions G n) z=0:= fun z=> (needles o) ▸ quiet g h hx hn z -- fix
    simpa only [wires,hessian_eq,map_sum,_root_.sum_apply] using hv (needle G y)
lemma col_zero {o:Site n}(hx:Nonwrapping X o)(hn:4≤n.val)(x:Site n):∑ y:Site n,wires f x y=0:= by unfold wires;simp_rw [hessian_symm h (needle G x)]; exact row_zero g h hx hn x -- simp loop

lemma catches {o:Site n} (hx:Nonwrapping X o)(hn:4≤n.val) : coeff f o axes01 axes01=judge f := by
   have ht : (∑ x:Site n,∑y:Site n, pitch x o^2*wires f x y)=0:= by simp_rw [← Finset.mul_sum,col_zero g h hx hn,mul_zero]; simp
   have hh : (∑ x:Site n,∑y:Site n,pitch y o^2*wires f x y)=0:= by rw [Finset.sum_comm];simp_rw [← Finset.mul_sum,row_zero g h hx hn,mul_zero]; simp
   have he (x y:Site n) : pitch x y^2*wires f x y=pitch x o^2*wires f x y+pitch y o^2*wires f x y-2*(pitch y o*(pitch x o*wires f x y)):= by
       by_cases hl : x∈X
       · by_cases hp : y∈X
         · rw [knit x y o (hx x hl) (hx y hp)]; ring
         rw [show wires f x y=0 from (hessian_symm h ..).trans (absent g h y x hp)]; ring
       rw [absent g h x y hl]; ring
   unfold judge
   simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum (a:=(2:ℝ))]
   change logHessian f ((wedge axes01 _).field _) _ = _; rw [← needle_field o]; simp_rw [wires,hessian_eq,map_sum,_root_.sum_apply, map_smul, smul_apply, smul_eq_mul]
   simp_rw [wires,hessian_eq] at hh ht
   rw [hh,ht]; ring_nf; rw [Finset.sum_comm]
end YM.RG01Estimate.Censor

import YM.RG11Proof.Travel.Boost

/-!
# Construct forward formal coupling and within-grade field flows

`Static β (-b)`. Solve homogeneous final flows; for preadjustment
see `Adjust` -- use an algebraic adjustment there before invoking full
CS flow. Only finite power demands, coupling expansion requires no parity.
Coefficient expressions here prove polynomial dependence on log-length at
all real s; simultaneous estimation along regulator/growing-scale trajectories
needs finite truncation and evaluation with the orders tracking powers of s
(from qexpan or kfar etc, not implicit here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Travel
open YM.RG11.Jets YM.RG11.Scale PowerSeries
open scoped Classical BigOperators Topology
variable {J:Type*}[Fintype J]
local notation "ps"=>PowerSeries ℝ
namespace Static
variable (K:Static J)

def rulers : Static (Fin 1) where
   β:=K.β
   b:=0
   quiet:=K.quiet
   still:=Jets.piece_zero _

def glide(s:ℝ):ps :=K.rulers.curve (fun _=>X) s 0
def aim (s:ℝ):Square J ps:=Matrix.of fun i j=> K.curve (fun z=>(1:Square J ps) z j) s i

def changeBy (s:ℝ):Change ℝ J:=⟨glide K s, aim K s⟩

 theorem d_ruler (s:ℝ)(k:ℕ): HasDerivAt (fun u:ℝ=>coeff k ((K.changeBy u).g))
     (coeff k (K.β*derivative ℝ (K.glide s))) s:=by
   have he:=solutions K.rulers (fun _=>X) s 0 k
   change HasDerivAt _ (coeff k (_ +∑ j:Fin 1,(0:ps)* _)) _ at he
   simp only [zero_mul,Finset.sum_const_zero,add_zero] at he; exact he

 theorem d_frame (s:ℝ)(k:ℕ)(i j:J): HasDerivAt (fun u:ℝ=>coeff k ((K.changeBy u).Z i j))
    (coeff k ((K.β • (flash (K.aim s))+K.b * K.aim s) i j)) s:=solutions K (fun z=>(1:Square J ps) z j) s i k

@[simp] theorem strikes: changeBy K 0=Change.one ℝ J:= by
   apply Change.ext
   · unfold changeBy glide Change.one; rw [K.rulers.starts]
   ext i j n; unfold changeBy aim Change.one; simp

 theorem lawful_glide (s:ℝ): (K.glide s).constantCoeff=0 ∧ tangent (K.glide s)=1:=by
    have he:= K.rulers.reach (fun _=>X) 1 s (0:Fin 1)
    change Through 1 (glide K s) ((∑ i∈Finset.range 2,(s^i/i.factorial:ℝ) • ((K.rulers.T^[i]) (fun _=>X))) 0) at he
    let p:Fin 1→ps:=fun _=>X
    have hr : ∑ i∈Finset.range 2,(s^i/i.factorial:ℝ) • ((K.rulers.T^[i]) p)=p+s • fun _=>K.β:=by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]; ext1 j; simp [T,throws,rulers,p]
    rw [hr] at he
    have hw(k :ℕ)(h:k≤1) := he k h
    change constantCoeff _=_ ∧ tangent _ = _
    rw [← coeff_zero_eq_constantCoeff_apply,hw _ (by decide),tangent,hw _ (by decide)]
    dsimp only [Pi.add_apply,Pi.smul_apply,p]; simp [K.quiet]; right; rw [←coeff_zero_eq_constantCoeff_apply,K.quiet 0 (by decide)]

def bolt (X:Square J ps):Square J ps:= Matrix.of fun i j=> (K.β * derivative ℝ (X i j))+∑ k,K.b i k * X k j

theorem at_column (i:ℕ)(b t:J): (bolt K)^[i] 1 b t = (K.T^[i]) (fun j=>(1:Square J ps) j t) b:=by
   induction i generalizing b with
   | zero=>rfl
   | succ i ih=>
     rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
     change _ + _ = _ + ∑ k, K.b b k * _
     simp_rw [ih]

 theorem swing (s:ℝ)(k:ℕ): piece k (K.aim s)=∑ i∈Finset.range (k+1), (s^i/i.factorial : ℝ) • piece k ((K.bolt^[i]) 1):=by
   ext a b; simp only [piece_apply, aim,Matrix.of_apply,K.finite_eq,Matrix.sum_apply,Matrix.smul_apply,rotor, Finset.sum_apply,map_sum,Pi.smul_apply,map_smul, at_column]

 theorem base (s:ℝ): nearId (K.aim s):=by unfold nearId; simp [swing]

private theorem paced {L:Constraints ℝ J}(he:vertical (L:=L) K.b){z:Square J ps}(h:L.Lawful z ∨ vertical (L:=L) z):
    vertical (L:=L) (K.bolt z):=by
    have hu:K.bolt z=K.β • flash z+K.b*z:= rfl -- Matrix.of defeq
    rw [hu]
    obtain h|h:=h
    · exact (vertical.waive _ (vertical.flash h)).add (he.right h)
    apply vertical.add
    · apply vertical.waive
      have he (k:ℕ): piece k (flash z)=((k+1:ℕ):ℝ) • piece (k+1) z:= Matrix.ext fun i j=>by simp [coeff_derivative,Matrix.smul_apply,mul_comm]
      intro n; rw [he]; exact L.vary.smul_mem _ (h _)
    intro k; rw [piece_mul]; exact Submodule.sum_mem _ (fun z _=>L.both (he _) (h _))

 theorem bolts {L:Constraints ℝ J}(h:vertical (L:=L) K.b)(s:ℝ):L.Lawful (K.aim s) where
    baseline := K.base s
    positive hk :=by
       rename_i k
       rw [swing]; refine Submodule.sum_mem _ (fun n hn=>Submodule.smul_mem _ _ ?_)
       by_cases hv:n=0
       · subst n; simp [hk.ne']
       have H(i:ℕ): L.Lawful ((K.bolt^[i]) 1) ∨ vertical (L:=L) ((K.bolt^[i]) 1):=by
          induction i with
          |zero=>exact Or.inl Constraints.Lawful.id
          |succ i ih=>rw [Function.iterate_succ_apply']; exact Or.inr (K.paced h ih)
       exact (H n).elim (fun h=>h.positive hk) (fun h=>h k)

 theorem graded_aim {w:J→ℕ}(h:graded w K.b)(s:ℝ):graded w (K.aim s):=
    (graded.asLaw (K.base s)).mpr (K.bolts (L:=Constraints.sameGrade w) (fun i=>by
       have H:graded w (piece i K.b):=graded.piece_all (A:=K.b) (w:=w) |>.mp (@h) i
       change Matrix.BlockTriangular _ _ ∧ Matrix.BlockTriangular _ _
       constructor
       · exact fun _ _ ht=>@H _ _ (ne_of_lt ht)
       exact fun _ _ ht=> @H _ _ (ne_of_gt ht)) s)

 theorem law {L:Constraints ℝ J}(he:vertical (L:=L) K.b)(s:ℝ): Change.Good L (K.changeBy s):=
   ⟨⟨(K.lawful_glide s).1, (K.lawful_glide s).2.symm ▸ isUnit_one⟩,K.bolts he s⟩
end Static
end YM.RG11.Travel

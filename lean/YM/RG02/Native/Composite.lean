import YM.RG02.Native.Jets

/-!
# True-length projective budgets on composites

Linear or nonlinear inside maps. Use before amplitudes & weights; keep
palette/ports and factorial (Faa costs) all explicit. Estimates no growth
in V, but potentially costs dependent on block & inverse choice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Native
open Function Filter Finset Lattice RG Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped BigOperators Classical Topology ContDiff
variable {α β γ A Z: Type}
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype α][Fintype β]
variable {n m:Side}

def assemble (U: Stalk α β ℝ n) : Ground α n → Ground β n:= fun x i=> U i x
def above (U:Stencil α β ℝ)(F:Stencil β γ Z) : Stencil α γ Z:= fun n i=> F n i ∘ assemble (U n)
def origin (t:ℕ)(U:Stencil α β ℝ) := ∀ n:Side,t≤n.val→ assemble (U n) 0=0
variable {U:Stencil α β ℝ}{F:Stencil β γ Z}
variable {t r k:ℕ}

lemma assemble_fair (hf:fair t r U)(n:Side)(hp:t≤n.val) : ContDiffAt ℝ r (assemble (U n)) 0:= contDiffAt_pi.mpr (hf n hp)
lemma found (hf:fair t r U)(hg:fair t r F)(ht:origin t U): fair t r (above U F):=by
    intro n hk i
    have he : ContDiffAt ℝ r (F n i) (assemble (U n) 0):= by rw [ht n hk]; exact hg n hk i
    exact he.comp 0 (assemble_fair hf n hk)

lemma views (hf:fair t r U)(hn:t≤n.val) {s:ℕ} (he:s≤r) (x:Fin s→Ground α n)(i:Leaf β n) :
    iteratedFDeriv ℝ s (assemble (U n)) 0 x i= iteratedFDeriv ℝ s (U n i) 0 x:=by
    let H := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Leaf β n=>ℝ) i
    have hh : iteratedFDeriv ℝ s (H ∘ assemble (U n)) 0 = H.compContinuousMultilinearMap (iteratedFDeriv ℝ s (assemble (U n)) 0):= H.iteratedFDeriv_comp_left (assemble_fair hf n hn) (Nat.cast_le.mpr he)
    exact (congr_arg (fun f=> (f : ContinuousMultilinearMap ℝ (fun _:Fin s=> Ground α n) ℝ) x) hh).symm -- edit

variable (U F)

def term (n:Side)(i:Leaf γ n)(c : OrderedFinpartition k)(v:Fin k→Ground α n) :=
    iteratedFDeriv ℝ c.length (F n i) 0 (fun m:Fin c.length=> iteratedFDeriv ℝ (c.partSize m) (assemble (U n)) 0 (v ∘ c.emb m))
variable {U F}
lemma stencil_law (hf:fair t r U)(hg:fair t r F)(ht:origin t U)(n:Side)(i:Leaf γ n)(hk:t≤n.val)(hy:k≤r) (v:Fin k→ Ground α n) :
    expand (shaped (above U F) k n) i v= ∑ c:OrderedFinpartition k,term U F n i c v:=by
    unfold shaped; rw [← shape_expanded]; unfold above
    have he : ContDiffAt ℝ r (F n i) (assemble (U n) 0):= by rw [ht n hk]; exact hg n hk i
    rw [iteratedFDeriv_comp he (assemble_fair hf n hk) (Nat.cast_le.mpr hy), ht n hk, FormalMultilinearSeries.taylorComp, _root_.sum_apply]; rfl

lemma through.above_works (hf:fair t r U)(hg:fair t r F)(ht:origin t U)(hu:through t r U)(hv:through t r F) : through t r (above U F):=by
    intro k hk; apply (receipt t _).mpr; intro n m h o i v hn
    rw [stencil_law hf hg ht n _ hn hk, stencil_law hf hg ht m _ (hn.trans (Nat.le_of_dvd m.pos h)) hk]; apply sum_congr rfl; intro c _
    let w:= fun z:Fin c.length=> iteratedFDeriv ℝ (c.partSize z) (assemble (U n)) 0 (v ∘ c.emb z)
    have hm := hn.trans (Nat.le_of_dvd m.pos h)
    have hy (z:Fin c.length) (a : Leaf β m): iteratedFDeriv ℝ (c.partSize z) (assemble (U m)) 0 ((weave α h o ∘ v) ∘ c.emb z) a=w z (collapse h o a):=by
       let x:=c.partSize z; have hx : x ≤ r:= (c.partSize_le z).trans hk
       unfold w; rw [views hf hm hx, views hf hn hx,shape_expanded, shape_expanded]; exact ((receipt t _).mp (hu x hx) n m h o a _ hn).symm
    change iteratedFDeriv ℝ _ _ _ w=_; unfold term; rw [show (fun z:Fin c.length=> iteratedFDeriv ℝ (c.partSize z) (assemble (U m)) 0 ((weave α h o ∘ v) ∘ c.emb z))=(weave β h o ∘ w) from funext fun z=>funext (hy z),shape_expanded,shape_expanded]
    exact (receipt t _).mp (hv c.length (c.length_le.trans hk)) n m h o i w hn

section fee
variable {F : Stencil β γ Z}
lemma term_components (hf:fair t r U){v: Fin k→ Leaf α n} (h:t≤n.val)(hk:k≤r){i:Leaf γ n}(c:OrderedFinpartition k) :
    term U F n i c (pulse ∘ v)=∑ a:Fin c.length→Leaf β n,(∏ m:Fin c.length,shaped U (c.partSize m) n (a m) (v ∘ c.emb m)) • shaped F c.length n i a:=by
    unfold term; rw [shape_expanded]; unfold expand; refine sum_congr ?_ ?_
    · ext; simp
    intro a _; congr 1
    exact prod_congr rfl fun m _=> views hf h ((c.partSize_le m).trans hk) _ _

-- `b` outside, `d` inside. sigma actual length chemistry.
def time (v:ℝ)(o:Site n)(x:Fin k→ Leaf α n) := Real.exp (v * spanAt o x)
omit [Fintype α] [Fintype β] in
lemma laws_time {v b d:ℝ} (hv:0≤v)(hq:v*k ≤ b)(hw:v≤d)(o:Site n)(c:OrderedFinpartition k) (j:Fin k→Leaf α n)(a:Fin c.length→Leaf β n) :
    time v o j ≤ time b o a * ∏ i:Fin c.length,time d (a i).1 (j ∘ c.emb i):=by
    unfold time; rw [← Real.exp_sum, ← Real.exp_add]; apply Real.exp_le_exp.mpr
    unfold spanAt; rw [← c.sum_sigma_eq_sum]
    simp_rw [Nat.cast_sum,Finset.mul_sum]
    rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _
    calc
       _ ≤ ∑ z:Fin (c.partSize i), (v * (separation (a i).1 o) + d* separation ((j ∘ c.emb i) z).1 (a i).1):= by
          apply sum_le_sum; intro z _
          have hx := separation_triangle (j (c.emb i z)).1 (a i).1 o
          calc
            _ ≤ v * (separation (j (c.emb i z)).1 (a i).1 + (separation (a i).1 o:ℝ)) := mul_le_mul_of_nonneg_left (by exact_mod_cast hx) hv
            _ ≤ _:=by rw [mul_add,add_comm]; exact add_le_add_right (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)) _
       _ ≤ _ := by
          rw [Finset.sum_add_distrib]; apply add_le_add_left; simp only [sum_const,card_univ, Fintype.card_fin,nsmul_eq_mul]; rw [← mul_assoc,mul_comm (c.partSize i:ℝ)]; exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (show (c.partSize i:ℝ)≤(k:ℝ) from by exact_mod_cast c.partSize_le i) hv).trans hq) (Nat.cast_nonneg _)

lemma fragments (c:OrderedFinpartition k){V : Type}[Fintype V] (u : ∀ i:Fin c.length,(Fin (c.partSize i) → V)→ ℝ):
    ∑ j:Fin k→V, (∏ i:Fin c.length,u i (j ∘ c.emb i))=∏ i:Fin c.length,(∑ j,u i j):=by
    let L : (Fin k→V) ≃ (∀ i:Fin c.length,Fin (c.partSize i)→V) := ((Equiv.arrowCongr c.equivSigma.symm (Equiv.refl V)).trans (Equiv.piCurry (fun (i:Fin c.length) (_:Fin (c.partSize i))=> V))) -- edit
    rw [Fintype.prod_sum,← L.sum_comp]; rfl

-- costs across the full composite. Charged without summing over
-- outer color. g factorials paid by callers. Through arbitrary finite r.
def total (P Q:ℕ→ℝ)(k :ℕ):= ∑ c:OrderedFinpartition k,P c.length * ∏ i:Fin c.length, Q (c.partSize i)

set_option maxHeartbeats 900000 in
lemma budget {b d v:ℝ}{P Q:ℕ→ℝ}(hh:0≤v)(he:k≤r)(hy:v*(k:ℝ) ≤ b)(hw:v≤d)
    (hf:fair t r U)(hg:fair t r F)(ht:origin t U)(hk:funded t r b F P)(hP:funded t r d U Q)(hQ:∀ k≤r,0≤Q k):
    charged t v (total P Q k) (shaped (above U F) k):=by
    intro n hn i
    let A(c:OrderedFinpartition k): ℝ:=P c.length*∏ i:Fin c.length,Q (c.partSize i)
    let C (c:OrderedFinpartition k):=(∑ j:Fin k→Leaf α n, time v i.1 j * ‖term U F n i c (pulse ∘ j)‖)
    have active (j:Fin k→Leaf α n) := stencil_law hf hg ht n i hn he (pulse ∘ j)
    have hu (m:OrderedFinpartition k): C m ≤ A m := by
       let f (j:Fin m.length→Leaf β n):=cost b (shaped F m.length n) i j
       let g (j:Fin m.length→Leaf β n)(z:Fin m.length)(u:Fin (m.partSize z)→ Leaf α n):= cost d (shaped U (m.partSize z) n) (j z) u
       have hhf(j:Fin m.length→Leaf β n): 0≤f j:= mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
       have hhg(j)(z:Fin m.length)(u):0≤g j z u:=mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
       let H(y: Fin k→Leaf α n)(j: Fin m.length→Leaf β n):= f j * ∏ z:Fin m.length,g j z (y ∘ m.emb z)
       unfold C A; calc
         _ ≤ ∑ y:Fin k→Leaf α n,∑ j:Fin m.length→Leaf β n,H y j:=by
            apply sum_le_sum; intro y _; rw [term_components hf hn he]
            apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Real.exp_pos _).le); rw [Finset.mul_sum]; apply sum_le_sum; intro j _
            let X:=∏ z:Fin m.length,shaped U (m.partSize z) n (j z) (y ∘ m.emb z)
            let Y:=shaped F m.length n i j
            apply le_trans (mul_le_mul_of_nonneg_right (laws_time hh hy hw i.1 m y j) (norm_nonneg (X • Y)))
            apply le_of_eq
            rw [norm_smul]; unfold X H f g; simp only [cost,Real.norm_eq_abs] -- want norm_prod
            simp_rw [abs_prod, Finset.prod_mul_distrib]; unfold time Y; ring
         _ ≤ _:=by
            rw [Finset.sum_comm]; let x:= ∏ i:Fin m.length,Q (m.partSize i)
            have hv(l:Fin m.length): 0≤Q (m.partSize l):= by -- maybe need β nonempty? NONE. hypothesize Q ≥ 0 in general
               exact hQ _ ((m.partSize_le l).trans he)
            calc
               _ ≤ ∑ j: Fin m.length→ Leaf β n, f j * ∏ i:Fin m.length, Q (m.partSize i):=by
                  apply sum_le_sum; intro j _; unfold H; rw [← Finset.mul_sum, fragments]; apply mul_le_mul_of_nonneg_left _ (hhf j); apply Finset.prod_le_prod (fun z _=>sum_nonneg (fun u _=> hhg j z u)); intro z _
                  apply le_trans _ (hP _ ((m.partSize_le z).trans he) n hn (j z)); apply le_of_eq
                  unfold ticket; apply sum_congr; ext; simp; exact fun _ _=>rfl
               _ ≤ _:=by
                  have hw:= hk _ (m.length_le.trans he) n hn i
                  rw [← Finset.sum_mul]; apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun j _=> hv j); apply le_trans _ hw; apply le_of_eq
                  unfold ticket; apply sum_congr; ext; simp; exact fun _ _=>rfl
    calc
       _ ≤ ∑ c:OrderedFinpartition k,C c:=by
          unfold C; rw [Finset.sum_comm]
          trans ∑ j:Fin k→Leaf α n, cost v (shaped (above U F) k n) i j
          · apply le_of_eq; unfold ticket; apply sum_congr; ext; simp; exact fun _ _=>rfl
          apply sum_le_sum; intro j _
          have hx:= active j; rw [samples] at hx
          unfold cost; rw [hx, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (Real.exp_pos _).le
       _ ≤ _:=sum_le_sum fun m _=> hu m

end fee
end YM.RG02.Native

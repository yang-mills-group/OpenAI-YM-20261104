import YM.RG06.Classical.Widen

/-!
# A triangular field-label *test* change on radial polynomial connections

Transforms ALL points, not just those accepted after Maxwell tests. Cut at `d`. Next project on
Maxwell free after using precisely this nonlinear change, to give a comparison of the **classical
stationary finite-jet relation**. Do not assume perturbative contractions or spikes respect it.
Recursion RTP, no division by g. Linearity / polynomiality in label components separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Function Analysis Continuum Tensor Vectorial Labels Maxwell
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius Topology
variable {G:Gauge}{d k:ℕ}

-- On *any* source of one homogeneous order use same operator to compute an
-- off-shell basis transformation. Preserve radial constraint (doesn't require source
-- conserved for that). Alternatively subtract linear combination of accepted responses with basis
-- projection on transverse source. Need polynomial linearity. Replicate short membership.
def retract(k:ℕ){f:Axis→E4→G.Color}(h:∀i,Level k (f i)): Taylor G (k+1):=
   ⟨fun i=>Tensor.coeff (chart k f i) (k+2) 0,(fun i=> Tensor.coeff_symm ((ContDiff.contDiffAt (all_chart h i).smooth).of_le (WithTop.coe_le_coe.mpr le_top))),
     fun x=> (Finset.sum_congr rfl (fun i (_:i∈ (Finset.univ:Finset Axis))=> congrArg (x i • ·) ((all_chart h i).indicates x))).trans (all_rad h x)⟩

/-- Power-map shift in each higher component, computed from lower d components only. -/
def invoice (g:ℝ)(J:Jet G)(k:ℕ):Taylor G (k+1):= retract k (fun i=> rate_part k (scene g (radField (k+2) J) i))
lemma offers(g:ℝ){J:Jet G}(H:YMAt g (k+2) J): offer k (invoice g J k)= data g (radField (k+2) J) k:=postage (prior g _ k H)
lemma visits (g:ℝ){A B:Jet G}(h:curt (k+1) A B): invoice g A k=invoice g B k:=by
 unfold invoice; congr 2
 -- dependent proof argument to retract
 have he:=cut (d:=k+2) (u:=A) (v:=B) (by exact h)
 rw [he]

def attire (g:ℝ)(J:Jet G): (i:ℕ)→Taylor G i
 | 0=>J 0
 | k+1=> J (k+1) - invoice g (fun i=> if _: i<k+1 then attire g J i else 0) k
termination_by i=>i

lemma accounts (g:ℝ)(A:Jet G)(k:ℕ):attire g A (k+1)=A (k+1)-invoice g (attire g A) k:=by
 rw [attire]; congr 1; exact visits g (fun i hi=>dif_pos hi)
lemma accounts_base (g:ℝ)(A:Jet G):attire g A 0=A 0:=by rw [attire]
lemma stays (g:ℝ){A B:Jet G}(h:curt k A B): curt k (attire g A) (attire g B) :=by
 intro i; induction i using Nat.strong_induction_on with | h i H=>
 intro hi
 rcases i with _|i
 · simp_rw [accounts_base,h 0 hi]
 rw [accounts,accounts,h _ hi,visits g (B:=attire g B) (k:=i) (fun j hj=>H j hj (hj.trans hi))]

-- inverse map computes with the very same K phase on previously stamped inputs
def out (g:ℝ)(J:Jet G):Jet G:=fun i=> match i with
 | 0=>J 0
 | k+1=>J (k+1) +invoice g J k

lemma depart (g:ℝ)(J:Jet G):out g (attire g J)=J:= by funext j; cases j with
                                                | zero=> exact accounts_base ..
                                                | succ j=> simp only [out, accounts, sub_add_cancel]
lemma return_home (g:ℝ)(J:Jet G):attire g (out g J)=J:=by
 funext i
 induction i using Nat.strong_induction_on with | h i H=>
 rcases i with _|i
 · simp only [accounts_base,out]
 rw [accounts,visits g (A:=attire g (out g J)) (B:=J) H]
 change J _ + _-_=_; rw [add_sub_cancel_right]
lemma weld (g:ℝ){A B:Jet G}(h:curt k A B):curt k (out g A) (out g B):=by
 intro i hi; rcases i with _|i
 · exact h _ hi
 have he:= h _ hi
 change _+invoice g A i=_+invoice g B i; rw [he]; exact congrArg _ (visits g (fun j hj=> h j (hj.trans hi)))

def physical(g:ℝ)(X:TaylorTower G):Jet G:=attire g (fun i=>gaugeJet (X i))
lemma turns (X:TaylorTower G)(g:ℝ)(d:ℕ): YMAt g d (physical g X):=by
 induction d with
 | zero=>exact fun _ h=>False.elim (by omega)
 | succ d H=>
    cases d with
    | zero=>exact fun _ h=>False.elim (by omega)
    | succ d=>
      cases d with
      | zero=>exact fun _ h=>False.elim (by omega)
      | succ d=>
         rw [rises]; refine ⟨H,?_⟩
         let A:=fun i=>gaugeJet (X i)
         change offer d (attire g A (d+1))=_; rw [accounts, sub_eq_add_neg, offer_add,offer_shell,offer_neg,zero_add]; exact congrArg Neg.neg (offers g H)

theorem invert_shell(g:ℝ)(J:Jet G)(k:ℕ)(h:YMAt g k J)(i:ℕ)(hi:i+2≤k):∃ v:Shell G i,gaugeJet v=out g J i:=by
 rcases i with _|i
 · exact rooms _
 have he:= (rises g i J).mp (reflects g J (show i+3≤k by omega) h)
 let p:=out g J (i+1)
 have hm:offer i p=0:=by unfold p out;rw [offer_add, offers g he.1,he.2,neg_add_cancel]
 exact ⟨shelf p hm,reference ..⟩
lemma settled (g:ℝ){J:Jet G}: YMAt g d J ↔ ∃ X:TaylorTower G,curt (d-1) J (physical g X):=by
 constructor
 · intro h
   have he(i:ℕ):∃ v:Shell G i,i+2≤d→gaugeJet v=out g J i:=by
      by_cases hi:i+2≤d
      · obtain ⟨v,hv⟩:=invert_shell g J d h i hi; exact ⟨v,fun _=>hv⟩
      exact ⟨0,fun h=>False.elim (hi h)⟩
   choose v hv using he
   refine ⟨v,?_⟩
   rw [← return_home g J]; apply stays
   intro i hi; exact (hv i (by omega)).symm
 intro ⟨v,he⟩; unfold YMAt; rw [cut he]; exact turns v g d
end YM.RG06.ClassicalOn

import YM.X.Reed.Twig
/-! # Prepare the difference descent. Use ∗explicit∗ K-projector via highest differences.
Done on the lift even for periodic lines using only local data.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {V : Type*} [NormedAddCommGroup V][NormedSpace ℝ V] {n:ℕ}
def jumped (l:Fin n→Axis): (Cover→V) →ₗ[ℝ] Cover→ V where
    toFun f:= jumps n l f;map_smul' r f:= jumps_scale ..;map_add' f g:=jumps_add ..
lemma jumpIt (l:Fin n→Axis)(f:Cover→V): jumped l f=jumps n l f:= rfl

def catchP (n:ℕ)(j : Axis)(A:Brush G): T E4 G.Color n:= seed (fun l:Fin n→Axis=> ((↑n.factorial):ℝ)⁻¹ • jumps n l (raising j A) 0)
def seeP (n:ℕ)(A:Brush G) : Specs G n:=⟨fun i=> catchP n i A,by
   intro i _ v s; let p:=catchP n i A; have he:p.domDomCongr s=p:= by
      apply seedEq; intro l; change catchP n i A (YM.basis ∘ (l∘s))= catchP n i A _; simp only [catchP,fertile,jump_sym]
   exact congr_arg (fun Z:T E4 G.Color n=> Z v) he⟩
def port (n:ℕ) : Specs G n→ₗ[ℝ] Brush G:= skew n ∘ₗ (evenShape n).subtype
lemma eg (p:Specs G n)(j:Axis): raising j (port n p)=reach (tip j) (p.val j):= rfl
lemma earns (l:Fin n→Axis)(A:Brush G)(j:Axis)(z:Cover): jumps n l (raising j (port n (seeP n A))) z = jumps n l (raising j A) 0:= by
   rw [eg, top ((seeP n A).sym j)]; change (n.factorial:ℝ) • catchP n j A _=_; rw [catchP,fertile,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
lemma gone (l:Fin n→Axis)(A:Brush G)(j:Axis):
    jumps n l (raising j (A-port n (seeP n A))) 0=0:= by rw [map_sub,jumps_sub,Pi.sub_apply,earns,sub_self]
lemma against {n:ℕ}(p:Okay G n) : downKG _ p.val=0:= p.property
abbrev launch (p:Okay G n):Brush G:= port n p.val
lemma lif (p:Okay G n): valP _ p= launch p:= rfl
lemma K_bound (p:Okay G n)(j:Axis) : orderK j (launch p)=0:= congr_fun (against p) j

-- K difference identity stencil. test on ∗jumps∗ of residual.
omit [NormedSpace ℝ V] in
lemma jump_shift (l:Fin n→Axis)(f:Cover→V)(z t:Cover): jumps n l (fun q=> f (q+t)) z= jumps n l f (z+t):= by
   induction n generalizing f with
   | zero=> rfl
   | succ n IH=>
       rw [jumps,jumps]; have he(i:Axis): stepValue (fun q=>f (q+t)) i = fun q=>stepValue f i (q+t):= by funext q;unfold stepValue; rw [add_right_comm];
       rw [he]; exact IH _ _
lemma next_K (j:Axis)(l:Fin n→Axis)(A:Brush G)(z:Cover):
    jumped l (orderK j A) z= -∑ i:Axis,
       (jumps (n+2) (Fin.cons i (Fin.cons i l)) (raising j A) (z-step i) - jumps (n+2) (Fin.cons j (Fin.cons i l)) (raising i A) (z-step i)):= by
   simp only [orderK,LinearMap.neg_apply,LinearMap.sum_apply, map_neg,map_sum, Pi.neg_apply, Finset.sum_apply,LinearMap.comp_apply]; congr 1;apply sum_congr rfl; intro i _;rw [jumpIt,steps,steps,steps]
   rw [show rewinds i (curlL i j A)= fun q=> stepValue (curlL i j A) i (q+-step i) by funext; unfold rewinds rewind; simp [sub_eq_add_neg],jump_shift, ← sub_eq_add_neg];
   rw [steps]; change jumps n l (stepValue (stepValue (raising j A) i-stepValue (raising i A) j) i) _ = _; rw [show stepValue (stepValue (raising j A) i-stepValue (raising i A) j) i=stepValue (stepValue (raising j A) i) i -stepValue (stepValue (raising i A) j) i from jumps_sub 1 (fun _=>i) _ _,jumps_sub]; rfl

-- measure K on highest shifts using same finite testers
abbrev Line (G:Gauge)(n:ℕ):= Axis → (Fin n→Axis)→ G.Color
def seethe (n:ℕ): Specs G n →ₗ[ℝ] Line G (n-2) := LinearMap.pi fun j:Axis=> LinearMap.pi fun l:Fin (n-2)→Axis=> (LinearMap.proj (0:Cover)) ∘ₗ (jumped l) ∘ₗ (orderK j) ∘ₗ (port n)
lemma sizzle (n:ℕ)(p: Specs G (n+2))(j:Axis)(l:Fin n→Axis): seethe (n+2) p j (fun i: Fin (n+2-2)=> l (i.cast (by omega)))= jumps n l (orderK j (port _ p)) 0:= by
    have he (A:Cover→G.Color) (k:ℕ)(e:k=n): jumps k (fun i=> l (i.cast e)) A 0=jumps n l A 0:= by subst k; rfl
    apply he
lemma seethe_ker (n:ℕ): LinearMap.ker (seethe (G:=G) n) = LinearMap.ker (downKG (G:=G) n):= by
    refine le_antisymm (fun p hp=>?_) (fun p hp=>?_)
    · cases n with
      | zero=> exact funext (heat_root p)
      | succ n=> cases n with
        | zero=> exact funext (heat_low p)
        | succ n=>
          apply (down_condition p).mpr ((cool _ (trot_closed p)).mpr _) -- tactic apply?
          intro j; apply seedEq; intro i; let X:= heat j (trot p.val)
          have he : jumps n i (orderK j (skew _ p.val)) 0=0:= (sizzle _ p j i).symm.trans (congr_fun (congr_fun (LinearMap.mem_ker.mp hp) j) _)
          have hu : (n.factorial:ℝ) • X (basis ∘ i)=0:= by rw [heat_K,map_neg,jumps_neg,Pi.neg_apply,top (heat_sym _ _ (trot_closed p)),neg_eq_zero] at he; exact he
          exact (smul_eq_zero.mp hu).resolve_left (by positivity)
    change seethe n p=0; funext i j; change jumped _ (orderK i _) _= _; rw [show orderK i (port _ p)=0 from congr_fun (LinearMap.mem_ker.mp hp) i, map_zero]; rfl

open Asymptotics LinearMap
variable {E' F' : Type*}[NormedAddCommGroup E'][NormedAddCommGroup F'][NormedSpace ℝ E'][NormedSpace ℝ F']
local notation "R"=> (atTop:Filter ℕ)
lemma bridgeK (L:E'→ₗ[ℝ] F')(Y : Submodule ℝ E') [FiniteDimensional ℝ F'](he: ker L= Y):∃ B:E'→ₗ[ℝ] Y, ∀ f:ℕ→E', ∀ c:ℕ→ℝ, (L ∘ f)=O[R] c → (fun k=> f k-(B (f k)).val)=O[R] c:= by
    subst Y; obtain ⟨Z,H⟩:= L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
    let g:= L.rangeRestrict
    let B:E' →ₗ[ℝ] E':= LinearMap.id-(Z ∘ₗ g)
    have h : ∀ p:E', B p ∈ ker L:= by
       intro p; rw [← ker_rangeRestrict] -- name
       change g (p-Z (g p))=0; rw [map_sub,show g (Z (g p))=g p from LinearMap.congr_fun H (g p),sub_self]
    refine ⟨B.codRestrict _ h,fun f c hf=>?_⟩; have he : (g ∘ f)=O[R] c:= by
       apply isBigO_iff.mpr; obtain ⟨m,hm⟩:= isBigO_iff.mp hf; exact ⟨m,hm⟩ -- norm defeq
    refine ((Z.toContinuousLinearMap.isBigO_comp (g ∘ f) R).trans he).congr_left (fun k=> ?_); change Z (g (f k))= f k-(f k-Z (g (f k))); abel
set_option maxHeartbeats 700000 in
lemma keeper (n:ℕ):∃ B:Specs G n →ₗ[ℝ] Okay G n, ∀ f:ℕ→Specs G n, ∀ c:ℕ→ℝ, (seethe n ∘ f)=O[R] c→ (fun k=> f k-(B (f k)).val)=O[R] c:= by
    have h:=bridgeK (E':=Specs G n) (F':=Line G (n-2)) (seethe (G:=G) n) (LinearMap.ker (downKG (G:=G) n)) (seethe_ker (G:=G) n)
    exact h
def strikeP (n:ℕ): Specs G n→ₗ[ℝ] Okay G n:= (keeper n).choose
lemma shoots {f:ℕ→Specs G n}{c:ℕ→ℝ}(hf: (seethe n ∘ f)=O[R] c) : (fun k=>f k-(strikeP n (f k)).val)=O[R] c:= (keeper n).choose_spec f c hf
end YM.PositionX.Reed

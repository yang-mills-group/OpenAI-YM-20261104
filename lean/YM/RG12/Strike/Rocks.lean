import YM.RG12.Strike.Moment
/-!
# List tensor version of the angular charge
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Finset MeasureTheory Real
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {n m:ℕ}
abbrev Cells:= List Axis4
structure Rated (n:ℕ)(P:Cells→ℂ):Prop where
    sym {u v:Cells} (h:List.Perm u v) : u.length=n→P u=P v
    clean {u:Cells} : u.length+2=n → ∑ i:Axis4,P (i::i::u)=0
abbrev gauge (n:ℕ)(P:Cells→ℂ): Strip n→ℂ := P ∘ List.ofFn
-- convert `Rated` proof - reext with two cells first via permutation
lemma carved (r:ℕ){P:Cells→ℂ}(H:Rated r P): Cloud (gauge r P):=by
   constructor
   · intro t v
     exact H.sym (t.ofFn_comp_perm v) (by simp)
   intro i j v hi
   cases r with
   | zero=> exact Fin.elim0 i
   | succ n=>
     cases n with
     | zero=> haveI : Subsingleton (Fin (0+1)):=inferInstanceAs (Subsingleton (Fin 1)); exact (hi (Subsingleton.elim i j)).elim
     | succ n=>
       let I:=n+2
       -- sigma making 0->i,1->j
       let s:=Equiv.swap 0 i; let r':Fin I:=s.symm j
       have hR:r'≠0:= fun h=> hi ((by rw [← s.apply_symm_apply j, show s.symm j=r' from rfl, h];simp [s]) : i=j)
       let t:Equiv.Perm (Fin I):=(Equiv.swap 1 r').trans s
       have he : (1:Fin I)≠0:= fun h=> Fin.succ_ne_zero (0 : Fin (n+1)) h
       have h0:t 0=i:=by
          have hx:Equiv.swap (1:Fin I) r' 0=0:=Equiv.swap_apply_of_ne_of_ne he.symm hR.symm
          change s (Equiv.swap _ r' 0)=_; rw [hx];simp [s]
       have h1:t 1=j:=by simp only [t,r', Equiv.trans_apply,Equiv.swap_apply_left, s.apply_symm_apply]
       let G(x:Axis4):= update (update v i x) j x
       have ha(x:Axis4): gauge I P (G x)=gauge I P (G x ∘ t):= (H.sym (t.ofFn_comp_perm (G x)) (by simp)).symm
       let f(k:Fin n):= t (k.succ.succ)
       have hz(k:Fin n): f k ≠ i ∧ f k ≠ j:=by
          rw [← h0,← h1]; constructor
          · exact t.injective.ne (Fin.succ_ne_zero _)
          exact t.injective.ne (fun h=> Fin.succ_ne_zero k (Fin.succ_injective _ (show k.succ.succ = (0:Fin (n+1)).succ from h)))
       let L:=List.ofFn (v∘f)
       have hv(x:Axis4):gauge I P (G x ∘t)=P (x::x::L):=by
          unfold gauge; rw [Function.comp_apply]; apply congrArg P
          rw [List.ofFn_succ,List.ofFn_succ]
          have hG(k:Fin n): (G x ∘ t) k.succ.succ=v (f k):=by change update (update v i x) j x (f k)=_; simp only [Function.update_of_ne (hz k).2, Function.update_of_ne (hz k).1]
          change (G x (t 0)::G x (t 1):: _) = _
          erw [h0,h1]; congr 1
          · simp [G,hi]
          simp only [G,Function.update_self]; congr 1
          exact congr_arg List.ofFn (funext hG)
       change ∑x:Axis4,gauge I P (G x)=0
       simp_rw [ha,hv]; exact H.clean (by simp [L,I])

def sun (v:Cells)(x:R):ℂ:=(v.map (fun i:Axis4=>(x i:ℂ))).prod
lemma sun_nil (x:R):sun [] x=1:=by simp [sun]
lemma sun_step (i:Axis4)(v:Cells)(x:R):sun (i::v) x= (x i:ℂ)* sun v x:=by simp [sun]
lemma sun_join (v u:Cells)(x:R): sun v x* sun u x=sun (v++u) x:=by simp [sun]
lemma sun_cont (v:Cells):Continuous (sun v):=by
  induction v with
  | nil=> exact continuous_const
  | cons a l he=>
     unfold sun; simp only [List.map_cons,List.prod_cons]; have hh:Continuous (fun x:R=> (x a:ℂ)):=by fun_prop
     exact hh.mul he
lemma sun_ofFn (v:Strip n)(x:R): rain v x=sun (List.ofFn v) x:=by rw [sun,List.map_ofFn,List.prod_ofFn]; rfl
lemma shave {w:R→ℂ}(hw:Round w)(n:ℕ): ∃ c:ℂ,∀ P:Cells→ℂ, Rated n P →∀ v:Cells,v.length≤n→ (∫ x:R,w x * fall (gauge n P) x *sun v x) = if v.length=n then c*P v else 0:=by
   obtain ⟨c,Hc⟩:= closure (n:=n) hw
   refine ⟨c,fun P h v he =>?_⟩
   let f:= v.get
   have hs(x:R) : sun v x=rain f x:=by rw [sun_ofFn, List.ofFn_get]
   simp_rw [hs]; split
   · next h'=> cases h'; rw [Hc _ (carved _ h)]; unfold gauge f; rw [Function.comp_apply,List.ofFn_get] -- office nonsense
   next hf=> exact below (P:=gauge n P) (carved n h) hw f (Nat.lt_of_le_of_ne he hf)
end YM.RG12.Strike

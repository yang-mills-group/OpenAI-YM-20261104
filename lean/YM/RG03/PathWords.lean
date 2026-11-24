import YM.RG03.WalkReduction

/-!
# Polynomial-cost canonicalization through one additional curvature degree

At one common root. Exact identities at every U. Prefixes represent true walks on the lifted
lattice, without reducing lengths modulo the torus. No changes to hard masks implicit here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03
namespace PathWords
open RG Wiring Wilson Lattice
open scoped Matrix.Norms.Frobenius Classical BigOperators
variable {G:Gauge} {n:Side}

abbrev Word := List Circuit

def value (w:Word) (o:Site n) (U:Config G n) : G.Mat := (w.map fun c => c.defect o U).prod
def total (X:List Word) (o:Site n) (U:Config G n) : G.Mat := (X.map fun w => value w o U).sum

def short (w:Word) (l:ℕ) := ∀ c∈w, c.prefix'.length ≤ l
lemma short.more {w:Word} {l k : ℕ} (h:short w l) (he:l≤k) : short w k := fun i hi => (h i hi).trans he

@[simp] lemma value_nil (o:Site n) (U:Config G n) : value [] o U=1 := rfl
@[simp] lemma value_cons (c:Circuit)(w:Word)(o:Site n)(U:Config G n) : value (c::w) o U=c.defect o U*value w o U := rfl
@[simp] lemma value_append (a b:Word)(o:Site n)(U:Config G n) : value (a++b) o U=value a o U*value b o U := by simp [value]
@[simp] lemma total_nil (o:Site n)(U:Config G n) : total [] o U=0 := rfl
@[simp] lemma total_cons (a:Word)(b:List Word)(o:Site n)(U:Config G n) : total (a::b) o U=value a o U+total b o U := rfl
@[simp] lemma total_append (a b:List Word)(o:Site n)(U:Config G n) : total (a++b) o U=total a o U+total b o U := by simp [total]

private def triples (r s : Walk) (u v a b : Step) : List Word :=
  let z := Circuit.mk r u v
  let y := Circuit.mk r v u
  let x := Circuit.mk ((r++[v,u])++s) a b
  [[z,x],[x,y],[z,x,y]]

private lemma erase_at_prefix (r s:Walk)(a:Step)(i j : Step)(o:Site n)(U:Config G n) :
   (Circuit.mk (r++[a,a.rev]++s) i j).defect o U=(Circuit.mk (r++s) i j).defect o U := by
  have he (x : Site n) : stop x [a,a.rev]=x := by rw [stop,stop,stop, Step.vec_rev]; simp
  have hg (x : Site n) : travel U x [a,a.rev]=1 := by simp [travel]
  unfold Circuit.defect Circuit.raw; rw [Circuit.holonomy_eq,Circuit.holonomy_eq]; unfold Circuit.start
  simp only [travel_append,stop_append,he,hg,mul_one]

private lemma duplicate_at_prefix (r s:Walk) (i j : Step) (he:stop (0:Cover) r=stop 0 s)
    (o:Site n)(U:Config G n) :
    (Circuit.mk (r++Lattice.reverse s++s) i j).defect o U=(Circuit.mk r i j).defect o U := by
  have hu : stop o r=stop o s := by rw [lift_stop,lift_stop,he]
  have ht : stop o (r++Lattice.reverse s)=o := by rw [stop_append,hu,reverse_stop]
  have hg : travel U o ((r++Lattice.reverse s)++s)=travel U o r := by rw [travel_append,travel_append,ht,hu,travel_reverse]; group
  unfold Circuit.defect Circuit.raw; rw [Circuit.holonomy_eq,Circuit.holonomy_eq]; unfold Circuit.start; simp only [stop_append,hu,reverse_stop,hg]

/-- Only the unchanged-degree term is followed along the *whole* path chain. Thus only
polynomially many higher words are output, ready for a separate pass on the remaining finite
degrees. -/
theorem chain_single {l k:ℕ}{r s:Walk}(h:Chain l r s k)(i j:Step) (o:Site n)(G:Gauge) : ∃ X : List Word,
    (∀ w∈X, 2 ≤ w.length ∧ w.length ≤ 3 ∧ short w l) ∧ X.length ≤ 3*k ∧
    ∀ U:Config G n, (Circuit.mk r i j).defect o U=(Circuit.mk s i j).defect o U+ total X o U := by
  induction h with
  | idle w h => refine ⟨[], (by simp), Nat.zero_le _, (fun U => by rw [total_nil,add_zero])⟩
  | erase a b c h => exact ⟨[],(by simp),Nat.zero_le _,(fun U=>(erase_at_prefix a b c i j o U).trans (by rw [total_nil,add_zero]))⟩
  | swap a b c d h =>
    have hr : a.length ≤ l := by simp only [List.length_append,List.length_cons,List.length_nil] at h; omega
    have hs : ((a++[d,c])++b).length ≤ l := (by simpa only [List.length_append,List.length_cons,List.length_nil] using h)
    refine ⟨triples a b c d i j,?_,by simp [triples],?_⟩
    · intro w hw; simp only [triples,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with hw|hw|hw
      all_goals subst w; simp [short,hr]; simpa using hs
    intro U
    change (afterSwap a b c d i j).defect o U = (afterSwap a b d c i j).defect o U + _
    rw [defect_align a b c d i j U o]
    simp only [triples,total_cons,value_cons,value_nil,total_nil]
    unfold incrementMat afterSwap; noncomm_ring
  | @trans a b c e v h h' ih ih' =>
    obtain ⟨X,hX,hL,hU⟩:=ih
    obtain ⟨Y,hY,hM,hW⟩:=ih'
    refine ⟨X++Y,fun w hw=>(List.mem_append.mp hw).elim (hX w) (hY w),?_ ,fun U=>?_⟩
    · rw [List.length_append]; omega
    rw [hU,hW,total_append]; abel

def similar (a b : Circuit) : Prop :=
    a.a=b.a ∧ a.b=b.b ∧ stop (0:Cover) a.prefix'=stop 0 b.prefix'
def paired := List.Forall₂ similar

theorem lift_single {r s : Circuit} (he:similar r s) {l:ℕ} (hr : short [r] l) (hs : short [s] l)
   (G:Gauge)(o:Site n) : ∃ X : List Word,
   (∀ w∈X, 2 ≤ w.length ∧ w.length ≤ 3 ∧ short w (3*l)) ∧ X.length ≤ 12*l^2 ∧
   ∀ U:Config G n,r.defect o U=s.defect o U+total X o U := by
  rcases r,s with ⟨⟨r,i,j⟩,s,ii,jj⟩
  obtain ⟨rfl',rfl'',he⟩:=he
  cases rfl'; cases rfl''
  obtain ⟨e,hE,h⟩:=same_lift r s he
  obtain ⟨X,hX,hL,hU⟩:=chain_single h _ _ o G -- steps must infer from hU? placeholders?
  have hr' : r.length ≤ l := hr _ List.mem_cons_self
  have hs' : s.length ≤ l := hs _ List.mem_cons_self
  have hm : r.length+2*s.length ≤ 3*l := by omega
  refine ⟨X,fun w hw=>?_ , (hL.trans (Nat.mul_le_mul_left _ hE)).trans ?_,fun U=>?_⟩
  · have H:=hX w hw; exact ⟨H.1,H.2.1,H.2.2.more hm⟩
  · calc
      _ ≤ 3*(l+l)^2 := by gcongr
      _ = _ := by ring
  exact (duplicate_at_prefix r s _ _ he o U).symm.trans (hU U)

private lemma total_right (X:List Word)(w:Word)(o:Site n)(U:Config G n):
    total (X.map (·++w)) o U = total X o U * value w o U := by
  induction X with
  | nil => simp
  | cons x X ih => simp [ih, add_mul]
private lemma total_left (c:Circuit)(X:List Word)(o:Site n)(U:Config G n):
    total (X.map (c::·)) o U = c.defect o U * total X o U := by
  induction X with
  | nil => simp
  | cons x X ih => simp [ih,mul_add]

theorem lift_words (G:Gauge)(o:Site n) (r s : Word){l:ℕ} (he:paired r s) (hr:short r l) (hs:short s l) :
    ∃ X : List Word, (∀ w∈X, r.length+1 ≤ w.length ∧ w.length ≤ r.length+2 ∧ short w (3*l)) ∧
      X.length ≤ 12*l^2*r.length ∧ ∀ U:Config G n, value r o U=value s o U+total X o U := by
  change List.Forall₂ similar r s at he
  induction he with
  | nil => exact ⟨[],(by simp),Nat.zero_le _,(fun U=> by rw [total_nil,add_zero])⟩
  | @cons a b r s h h' ih =>
    obtain ⟨X,hX,hL,hU⟩:=lift_single h (l:=l) (fun c hc => (show c=a from by simpa using hc) ▸ hr _ List.mem_cons_self) (fun c hc => (show c=b from by simpa using hc) ▸ hs _ List.mem_cons_self) G o
    have hr' : short r l := fun c hc=>hr c (List.mem_cons_of_mem a hc)
    obtain ⟨Y,hY,hM,hV⟩:=ih hr' (fun c hc=>hs c (List.mem_cons_of_mem b hc))
    have hh (x s : ℕ)(h:x≤s) : x≤3*s := by omega
    refine ⟨(X.map (·++r))++(Y.map (b::·)),fun w hw=>?_,?_,fun U=>?_⟩
    · rcases List.mem_append.mp hw with he|he
      · obtain ⟨z,hz,rfl⟩:=List.mem_map.mp he; obtain ⟨hq,hq',hr⟩:=hX z hz
        refine ⟨by simp;omega,by simp;omega,?_⟩
        exact fun i hi=>(List.mem_append.mp hi).elim (hr i) ((hr'.more <| hh _ _ le_rfl) i)
      obtain ⟨z,hz,rfl⟩:=List.mem_map.mp he; obtain ⟨hq,hq',hr⟩:=hY z hz
      refine ⟨by simp;omega,by simp;omega,?_⟩
      exact fun i hi=>(List.mem_cons.mp hi).elim (fun H=>H ▸ (hs.more (hh _ _ le_rfl)) _ List.mem_cons_self) (hr i)
    · simp only [List.length_append,List.length_map,List.length_cons]; rw [mul_add,mul_one]; omega
    calc value (a::r) o U = b.defect o U * value r o U + total X o U * value r o U := by rw [value_cons,hU,add_mul]
         _ = b.defect o U * (value s o U + total Y o U) + total X o U * value r o U := by nth_rw 1 [hV]
         _ = _ := by rw [total_append,total_left,total_right,value_cons,mul_add]; abel
end PathWords
end YM.RG03

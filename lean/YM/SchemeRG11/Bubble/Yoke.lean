import YM.SchemeRG11.Bubble.Chair
/-!
Explicit 2-line loop typing. The input expression built in length-at-most-three i*momentum
moments. Use the standard generating Gaussian Schwinger-evaluation as a RULE,
not special integer-dimensional integrals defining an analytic continuation from
discrete points. Metric δ only with EXTERNAL or pinned indices. Gamma factors
already in factor. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Set MeasureTheory Filter Metric Function Hot MSbar
open scoped Topology ContDiff BigOperators
variable {n : ℕ}
/-- t1=ρt, p1=(1-ρ)p+r, t2=(1-ρ)t, p2=ρp-r -/
lemma completes (ρ t : ℝ) (p r : Space n) :
    (t*ρ)*‖r+(1-ρ)•p‖^2+(t*(1-ρ))*‖ρ•p-r‖^2 = t*‖r‖^2 + halo (t,ρ)*‖p‖^2 := by
  simp only [← real_inner_self_eq_norm_sq,inner_add_right,inner_add_left,real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right, real_inner_comm r p,halo,braid]; ring

structure Grain (n : ℕ) where
  /-- function of Schwinger parameter share λ -/
  w : ℝ→ℂ
  hw : Continuous w
  /-- momenta on p. -/
  shift : List (Fin n)
  /-- moments in r. -/
  rand : List (Fin n)

def readMom (p : Space n) (i : Fin n) := Complex.I*(p i:ℂ)
def letters (p : Space n) (l : List (Fin n)) := (l.map (readMom p)).prod

def earmark (i : Bool) (ρ : ℝ) : ℂ := if i then (1-ρ:ℝ) else ρ

def castShift (b : Bool × Fin n) (g : Grain n) : Grain n :=
    ⟨fun x=> g.w x*earmark b.1 x,g.hw.mul (by unfold earmark; split <;> fun_prop),b.2::g.shift,g.rand⟩
def rollSign (i : Bool) : ℂ := if i then 1 else -1

def castRoll (b : Bool × Fin n) (g : Grain n) : Grain n :=
    ⟨fun x=> g.w x*rollSign b.1,g.hw.mul continuous_const,g.shift,b.2::g.rand⟩
def grain : List (Bool × Fin n)→ List (Grain n)
| [] => [⟨fun _=>1,continuous_const,[],[]⟩]
| b::l => (grain l).flatMap fun g=>[castRoll b g,castShift b g]

def polished (X Y : List (Fin n)) := grain ((X.map (fun i=> (true,i))) ++ (Y.map (fun i=>(false,i))))
lemma valid (X Y : List (Fin n)) (h : X.length+Y.length≤3) : ∀ g∈polished X Y, g.rand.length≤3 := by
  have hh (l : List (Bool × Fin n)) : ∀ x∈ grain l,x.rand.length≤l.length:= by
    induction l with
    | nil => simp [grain]
    | cons b l ih =>
       intro x hx; simp only [grain, List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hx
       obtain ⟨g,hg,rfl|rfl⟩:=hx
       · exact Nat.succ_le_succ (ih g hg)
       exact (ih g hg).trans (Nat.le_succ _)
  intro g hg; exact (hh _ g hg).trans (by simpa only [List.length_append,List.length_map])

def Grained (g : Grain n) (ρ : ℝ) (p r : Space n) := g.w ρ*letters p g.shift * letters r g.rand
lemma shifted (X Y : List (Fin n)) (p r : Space n) (ρ : ℝ) :
    ((polished X Y).map (fun g=> Grained g ρ p r)).sum=letters (r+(1-ρ)•p) X*letters (ρ•p-r) Y := by
  let f (b:Bool × Fin n):= if b.1 then readMom (r+(1-ρ)•p) b.2 else readMom (ρ•p-r) b.2
  let E (g:Grain n):= Grained g ρ p r
  have hh (b : Bool × Fin n) (s:List (Grain n)): ((s.flatMap (fun g=>[castRoll b g,castShift b g])).map E).sum = f b*(s.map E).sum := by
    induction s with
    | nil => simp
    | cons g s ih =>
        simp only [List.flatMap_cons,List.map_append,List.sum_append,List.sum_cons,List.map_cons,List.map_nil,List.sum_nil,add_zero,ih,mul_add]
        congr 1
        cases hb : b.1 <;> simp [E,f,Grained,letters,hb,castRoll,castShift,readMom,earmark,rollSign] <;> ring
  have hi (l : List (Bool × Fin n)) : ((grain l).map E).sum=(l.map f).prod := by
     induction l with
     | nil => simp [grain,E,Grained,letters]
     | cons b l ih => simpa only [grain,List.map_cons,List.prod_cons] using (hh b (grain l)).trans (congrArg _ ih)
  unfold polished; rw [hi]; simp [letters,f,Function.comp_def]

structure Prize (n : ℕ) where
  w : ℝ→ℂ
  hw : Continuous w
  word : List (Fin n)
  rank : Bool

def reward (g : Grain n) : List (Prize n) := match g.rand with
| [] => [⟨g.w,g.hw,g.shift,false⟩]
| [i,j] => if i=j then [⟨fun x=> (-2:ℂ)⁻¹*g.w x,continuous_const.mul g.hw,g.shift,true⟩] else []
| _ => [] -- use only when g provenant from `valid`.

def Awards (X Y : List (Fin n)) := (polished X Y).flatMap reward
-- open normalized Gaussian moments in i*r, the only needed grades
def reads (t : ℝ) : List (Fin n)→ℂ
| [a,b] => if a=b then (-2*t:ℂ)⁻¹ else 0
| [] => 1
| _ => 0

lemma broker (X Y : List (Fin n)) (h : X.length + Y.length≤3) (t ρ : ℝ) (p : Space n) :
    ((Awards X Y).map fun s=> s.w ρ * letters p s.word * if s.rank then (t:ℂ)⁻¹ else 1).sum =
      ((polished X Y).map fun g=> g.w ρ * letters p g.shift * reads t g.rand).sum := by
  let f (s:Prize n):= s.w ρ* letters p s.word * if s.rank then (t:ℂ)⁻¹ else 1
  have hs (s:List (Grain n)) (hh : ∀ a∈s,a.rand.length≤3) : ((s.flatMap reward).map f).sum=(s.map fun g=>g.w ρ * letters p g.shift * reads t g.rand).sum := by
    induction s with
    | nil => rfl
    | cons g s ih =>
       have he : g.rand.length≤3:= hh _ (List.mem_cons_self)
       simp only [List.flatMap_cons,List.map_append,List.sum_append,ih (fun a ha=>hh _ (List.mem_cons_of_mem _ ha)),List.map_cons,List.sum_cons]; congr 1
       match hp : g.rand with
       | [] => simp [reward,hp,f,reads]
       | [_] => simp [reward,hp,f,reads]
       | [a,b] => by_cases H:a=b
                  · simp [reward,hp,f,H,reads]; ring
                  simp [reward,hp,f,H,reads]
       | [_,_,_] => simp [reward,hp,f,reads]
       | u::v::w::r::l => simp [hp] at he; omega
  exact hs _ (valid X Y h)
end YM.SchemeRG11.Bubble

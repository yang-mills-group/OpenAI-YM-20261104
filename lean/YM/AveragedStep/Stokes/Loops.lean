import YM.Wilson.Law
/-! # Any loop closed *on the cover*. Quantitative list of actual face
holonomies; the list may repeat sites or faces. No estimate by site count of
the torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.Loops
open Lattice Wilson
open scoped Classical BigOperators Matrix.Norms.Frobenius

/-- Same-axis squares in either sign contribute no face. -/
def token {R:Type*} [AddCommGroup R][One R] (a b:Step)(x:Four R) : List (Face R) :=
  if h:a.dir = b.dir then [] else [(atFace x a b,PlaqAxes.ordered a.dir b.dir h)]
def bill {R:Type*}[AddCommGroup R][One R]{G:Gauge}(U:Links R G.El)(l:List (Face R)):ℝ:=
  (l.map fun p=>G.chord (faceValue U p)).sum
@[simp] lemma bill_append {R:Type*}[AddCommGroup R][One R]{G:Gauge}(U:Links R G.El)(l k:List (Face R)) :
    bill U (l++k)=bill U l+bill U k:=by simp [bill]
lemma bill_pos {R:Type*}[AddCommGroup R][One R]{G:Gauge}(U:Links R G.El)(l:List (Face R)):
    0≤bill U l:=by
  induction l with
  | nil=> simp [bill]
  | cons a l ih=> exact (show (0:ℝ)≤G.chord (faceValue U a)+bill U l from add_nonneg (G.chord_nonneg _) ih)

variable {R:Type*} [AddCommGroup R][One R] {G:Gauge} (U:Links R G.El)
lemma oriented_bill (a b:Step)(x:Four R): G.chord (travel U x (oriented a b)) = bill U (token a b x):=by
  rw [price_shift_pos G.chord U G.chord_inv (fun k g=>G.chord_conj g k)]
  unfold token; split_ifs with h
  · rw [h]
    -- square on same dir literally backtracks
    let i:=b.dir; let y:=atFace x a b
    change G.chord (travel U y (square i i)) = _
    rw [show square i i=[posDir i,posDir i,(posDir i).rev,(posDir i).rev] from rfl]
    simp only [travel,Step.vec_rev,add_neg_cancel_right,Step.read_rev]; simp [bill]
    -- simpa with group_cancel
  rcases lt_or_gt_of_ne h with h|h
  · simp [bill,faceValue,PlaqAxes.ordered,min_eq_left h.le,max_eq_right h.le]
  simp only [bill, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, faceValue,
    PlaqAxes.ordered,min_eq_right h.le,max_eq_left h.le]
  change G.chord (travel U _ (oriented _ _))=G.chord (travel U _ (oriented _ _))
  rw [oriented_swap,G.chord_inv]

-- exact orientation of one local edit
lemma swap_bill (a b : Step) (w:Walk)(x:Four R):
    G.chord (travel U x (a::b::w)*(travel U x (b::a::w))⁻¹)= bill U (token a b x) := by
  rw [← oriented_bill]
  congr 1
  let y:=x+a.vec+b.vec
  simp only [Lattice.travel,oriented,mul_inv_rev,mul_one]
  rw [show x+b.vec+a.vec=y from add_right_comm x _ _]
  have h1:a.rev.read U y=(a.read U (x+b.vec))⁻¹:=by
    rw [show y=x+b.vec+a.vec from add_right_comm x _ _,Step.read_rev]
  rw [show x+a.vec+b.vec=y from rfl,h1,
    show y+a.rev.vec=x+b.vec by unfold y; rw [Step.vec_rev]; abel,Step.read_rev]
  group

def debt (a : Step) (x : Four R) : Walk → List (Face R)
  | []=>[]
  | b::l=>token a b x++debt a (x+b.vec) l
omit U in
lemma debt_length (a : Step)(x : Four R)(l : Walk): (debt a x l).length≤l.length := by
  induction l generalizing x with
  | nil=>rfl
  | cons b l ih=>
    rw [debt,List.length_append,List.length_cons,Nat.add_comm l.length]
    apply Nat.add_le_add _ (ih _)
    unfold token; split <;> simp

lemma slide (a : Step)(x : Four R)(l k:Walk):
    G.chord (travel U x (a::(l ++k)) * (travel U x (l++(a::k)))⁻¹) ≤ bill U (debt a x l):= by
  induction l generalizing x with
  | nil=>simp [debt,bill]
  | cons b l ih=>
    let p:=travel U x (a::b::(l++k)); let q:=travel U x (b::a::(l++k));
    let r:=travel U x (b::(l++a::k))
    change G.chord (p*r⁻¹) ≤ _
    rw [debt,bill_append,show p*r⁻¹=p*q⁻¹*(q*r⁻¹) by group]
    refine (G.chord_triangle _ _).trans (add_le_add (swap_bill U a b _ x).le ?_)
    unfold q r
    -- simplify only the common first step
    rw [show travel U x (b::a::(l++k))=b.read U x*travel U (x+b.vec) _ from rfl,
      show travel U x (b::(l++a::k))=b.read U x*travel U (x+b.vec) _ from rfl]
    rw [mul_inv_rev,mul_assoc (b.read U x),← mul_assoc (travel ..),←mul_assoc,G.chord_conj]
    exact ih _

private lemma stop_offset {R:Type*}[AddCommGroup R][One R](x y:Four R)(w:Walk):
    stop (x+y) w=x+stop y w:=by
  induction w generalizing y with
  | nil=> rfl
  | cons i w ih=> rw [stop,add_assoc,ih,stop]

omit U in
private lemma mate (i:Step){w:Walk}(h: stop (0:Cover) (i::w)=0):i.rev∈w:=by
  by_contra H
  -- i.dir coordinate cannot decrease in + case or increase in - case.
  rcases i with ⟨a,n|n⟩
  · change negDir a ∉ w at H
    suffices hs: ∀(w:Walk)(x:Cover), negDir a∉w→ x a ≤ (stop x w) a by
      have ht:=hs w ((0:Cover)+(posDir a).vec) H
      change stop ((0:Cover)+(posDir a).vec) w =0 at h
      rw [h] at ht; norm_num at ht
    intro w x he
    induction w generalizing x with
    | nil=> rfl
    | cons k w ih=>
      refine le_trans ?_ (ih (x+k.vec) (fun hu=>he (List.Mem.tail k hu)))
      rcases k with ⟨b,m|m⟩
      · simp [Step.vec]; split <;> simp
      have hh : b ≠ a:=by rintro rfl; exact he List.mem_cons_self
      simp [Step.vec,Ne.symm hh]
  change posDir a ∉ w at H
  suffices hs: ∀(w:Walk)(x:Cover), posDir a∉w→ (stop x w) a ≤ x a by
    have ht:=hs w ((0:Cover)+(negDir a).vec) H
    change stop ((0:Cover)+(negDir a).vec) w =0 at h
    rw [h] at ht; norm_num at ht
  intro w x he
  induction w generalizing x with
  | nil=> rfl
  | cons k w ih=>
    refine le_trans (ih (x+k.vec) (fun hu=>he (List.Mem.tail k hu))) ?_
    rcases k with ⟨b,m|m⟩
    · have hh : b≠a:=by rintro rfl; exact he List.mem_cons_self
      simp [Step.vec,Ne.symm hh]
    simp [Step.vec]; split <;> simp

omit U in
/-- The orientation list is determined before even the gauge group. Need
closure of the *walk* at zero in the cover regardless of periodic wrap
position; we aren't using small holonomy for winding links. -/
theorem closed (w:Walk)(h:stop (0:Cover) w=0)(x:Four R):
    ∃ l:List (Face R),l.length ≤ w.length^2 ∧ ∀ (G:Gauge)(U:Links R G.El),G.chord (travel U x w) ≤ bill U l := by
  induction e : w.length using Nat.strong_induction_on generalizing w x with
  | _ n ih=>
    cases w with
    | nil=> exact ⟨[],by simp,by intro G U; simp [travel,bill]⟩
    | cons i w=>
      obtain ⟨a,b,H⟩:=List.append_of_mem (mate i h)
      subst w
      have hd: stop (0:Cover) (a++b)=0:=by
        change stop (0+i.vec:Cover) (a++i.rev::b) =0 at h
        rw [stop_append,stop] at h
        rw [stop_append,zero_add, stop_offset, Step.vec_rev] at * -- stop_offset need i.vec+0
        have he (y:Cover)(q:Walk): stop y q=y+stop 0 q:= by
          simpa only [add_zero] using stop_offset y (0:Cover) q
        rw [he i.vec a,he (-i.vec) b,show i.vec+stop (0:Cover) a+(-i.vec+stop 0 b)=stop 0 a+stop 0 b from by abel] at h; rw [he (stop (0:Cover) a),h]
      have ht : (a++b).length < n := by simp [←e]
      obtain ⟨l,hl,hG⟩:= ih _ ht (a++b) hd x rfl
      refine ⟨debt i x a ++ l,?_,fun G U=>?_⟩
      · have hn:=debt_length i x a
        simp only [List.length_append,List.length_cons] at *; nlinarith [hl]
      rw [bill_append]
      let X:=travel U x (i::(a++i.rev::b)); let Y:=travel U x (a++i::i.rev::b)
      show G.chord X ≤ _
      rw [show X=(X*Y⁻¹)*Y from by group]
      refine (G.chord_triangle _ _).trans (add_le_add (slide U i x a (i.rev::b)) ?_)
      have hh : Y=travel U x (a++b):=by unfold Y; simp [travel_append,travel,Step.vec_rev]
      rw [hh];exact hG G U
end YM.AveragedStep.Loops

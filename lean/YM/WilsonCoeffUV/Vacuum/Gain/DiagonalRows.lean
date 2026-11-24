import YM.WilsonCoeffUV.Vacuum.Recursion
import YM.Next.FREE_KERNELS.Curl
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Newtown
/-!
# Pre-length leading diagonal transport rows through an order. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free MultiNext.SignedSource
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{P:Patch}{n c L f: Side}{α β : Type*}

-- simplify pack by area expose.
def parentC (L:Side) (x:Cover): Cover:= ((panel L Unit).symm (x,())).1
lemma castE (p: Cloth (Co L α)): (panel L α p)=(L.val • p.1+lift p.2.1,p.2.2):=rfl
lemma patchwork (i: Cloth α): (panel L α).symm i=(parentC L i.1,wrap L i.1,i.2):=by
    obtain ⟨⟨a,b,c⟩,rfl⟩:= (panel L α).surjective i
    rw [Equiv.symm_apply_apply,castE]; dsimp only; rw [show parentC L (L.val • a+lift b)=a from congr_arg Prod.fst ((panel L Unit).symm_apply_apply (a,b,()))]
    simp only [map_add,wrap_lift]; rw [show wrap L (L.val • a)=0 from ?ha,zero_add]
    case ha=>
      funext i; change ((((L.val • a):Cover) i:ℤ):ZMod L.val)=0; simp
lemma parent_pack (p: Cloth (Co L α)): parentC L (panel L α p).1=p.1:=by
  have he := (panel L α).symm_apply_apply p; rw [patchwork] at he; exact congr_arg Prod.fst he
lemma parent_stride (p q: Cover) : L.val*terrain.gap (parentC L p) (parentC L q) ≤ terrain.gap p q +8*L.val:=by
    let x:Fin 2→ Cloth (Co L Unit):=![(panel L Unit).symm (p,()), (panel L Unit).symm (q,())]
    have he:= cover_pack x; rw [drag_two,drag_two] at he; simpa [x,terrain,parentC] using he

def spring (L:Side)(M:ropes Cover (Co L α) β) : ropes Cover α β:= M.submatrix (panel L α).symm id
lemma route_cover (b:Cover)(r:Site L)(a:Cover):
    let i:= L.val • b +lift r ; (i+a) = L.val • (b+carry r a)+lift (arrives r a):= by
       intro i; unfold i; rw [add_assoc, carry_spec,smul_add]; abel
lemma flip_step (L:Side)(h:Odd L.val)(P : Cross L α β) (j:Axis)(x y:Cover)(b:α)(c:β):
     spring L (shuttleM (forwardC L P j)) (x,b) (y,c)= Newt.jump (fun x=> spring L (shuttleM P) (x,b) (y,c)) j x:=by
     obtain ⟨⟨a,r,k⟩,hk⟩:= (panel L α).surjective (x,b)
     rw [castE] at hk; obtain ⟨H,K⟩:= Prod.ext_iff.mp hk
     change L.val • a+lift r=x at H; change k=b at K; subst x k
     let p : Cover:= L.val • a+lift r; let d:= step j (S:=ℤ)
     have hv : (panel L α).symm (p,b)=(a,r,b):=(panel L α).symm_apply_apply (a,r,b)
     have he : (panel L α).symm (p+d,b)=(a+carry r d,arrives r d,b):= by apply (panel L α).injective; rw [Equiv.apply_symm_apply]; exact Prod.ext (route_cover a r d) rfl
     change shuttleM (forwardC L P j) ((panel L α).symm (p,b)) (y,c)=shuttleM P ((panel L α).symm (p+d,b)) (y,c)-shuttleM P ((panel L α).symm (p,b)) (y,c)
     rw [he,hv];
     unfold shuttleM forwardC
     rw [show arrives r d=r+step j by simp [arrives,d],carry_crank L h]; dsimp only
     rw [show y-a-(if lift r j = ((L.val/2:ℕ):ℤ) then step j else 0) = y-(a+carryStep j r) by change y-a-carryStep j r=_; abel]

-- coloration commutes
lemma color_step (M:PoleRows P)(w:List Axis): advanceC P.L (gaugedA G P M) w=gaugedA G P (advanceC P.L M w):=by
    induction w with
    | nil=>rfl
    | cons i w ih=>
      rw [advanceC,ih,advanceC]; ext ⟨a,p,j⟩ ⟨b,k⟩ v
      by_cases h:j=k <;> simp [forwardC,gaugedA,coloration,expandI,h]
      congr

lemma iter_append1 (F:Cover→ℝ)(v:List Axis)(i:Axis): Newt.iterate F (v++[i])= Newt.jump (Newt.iterate F v) i:= by induction v generalizing F<;> simp only [List.nil_append, List.cons_append,Newt.iterate, *]
lemma profit (L:Side)(h:Odd L.val)(M: Cross L α β)(v:List Axis)(o:Cover)(j:Cloth β)(a:α):
    (fun x=> spring L (shuttleM (advanceC L M v.reverse)) (o+x,a) j)= Newt.iterate (fun x=>spring L (shuttleM M) (o+x,a) j) v := by
    induction v using List.reverseRecOn with
    | nil=>rfl
    | append_singleton l i ih=>
      rw [List.reverse_append,List.reverse_singleton,List.singleton_append,advanceC,iter_append1,← ih]; funext x; rw [flip_step L h]; simp only [Newt.jump,add_assoc]

section stepCost
variable {Q:ropes Cover (Co L α) β}
-- bounds on all demanded forward differences with x offset in FINE. also explicit no α card.
def Crank (Q:ropes Cover (Co L α) β)(d:ℕ)(s C:ℝ): Prop:= 0≤C ∧ ∀ l:List Axis,l.length≤ d →∀ (o x:Cover)(a:α)(u:Cloth β), ‖Newt.iterate (fun z=>spring L Q (o+z,a) u) l x‖ ≤
    (C/(L.val:ℝ)^(1+l.length))*Real.exp (-s*terrain.gap (parentC L (o+x)) u.1)
variable {s t A C : ℝ}
lemma Crank.mono {d b:ℕ}(h:Crank Q d s A)(he:b≤d)(hp:t≤s): Crank Q b t A:=
    ⟨h.1,fun l hl o x a u=> (h.2 l (le_trans hl he) o x a u).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hp) (by positivity))) (div_nonneg h.1 (by positivity)))⟩
lemma Crank.below {d:ℕ}(h: Crank Q d s A)(i:Cloth α)(j): |spring L Q i j| ≤ (A/(L.val:ℝ))*Real.exp (-s*terrain.gap (parentC L i.1) j.1):= by
    have he:= h.2 [] (Nat.zero_le _) 0 i.1 i.2 j; simp_rw [Newt.iterate,List.length_nil,add_zero,pow_one,zero_add] at he; exact he
lemma Crank.polish {d:ℕ}(h:Crank Q d s A): dragCup terrain s (A/(L.val:ℝ)) Q:= by
   refine ⟨div_nonneg h.1 (by positivity),fun i j=>?_⟩
   have hp:= h.below (panel _ _ i) j; rw [parent_pack] at hp; unfold spring at hp; rw [Matrix.submatrix_apply,Equiv.symm_apply_apply] at hp; exact hp
lemma pack_clock (L:Side)(h:0≤s)(i j x:Cover){c:ℕ}(hv : terrain.gap i j ≤ c):
     Real.exp (-s*terrain.gap (parentC L j) x) ≤ Real.exp (8*s)*Real.exp ((s/L.val)*c)*Real.exp (-s*terrain.gap (parentC L i) x):=by
    simp only [← Real.exp_add]; apply Real.exp_monotone
    let p:= terrain.gap (parentC L i) (parentC L j)
    have H : ((terrain.gap (parentC L i) x:ℕ):ℝ)≤ p+(terrain.gap (parentC L j) x:ℝ):=by exact_mod_cast terrain.tri (parentC _ _) (parentC _ _) x
    have he : ((L.val:ℝ)*p) ≤ c+8*L.val:=by exact_mod_cast (parent_stride i j).trans (Nat.add_le_add_right hv _)
    have hb : s*p≤ 8*s+s/L.val*c:=by
      have hk:(L.val:ℝ)>0:=by positivity
      rw [div_mul_eq_mul_div, add_comm (8*s), ← sub_le_iff_le_add, le_div_iff₀ hk]
      nlinarith only [h,hk,H,he,mul_le_mul_of_nonneg_left he h]
    linarith only [hb,mul_le_mul_of_nonneg_left H h]
-- d≥? output remainder in total degree.
lemma Crank.tag {d:ℕ}(h:Crank Q d s C)(hp:0<s)(o x:Cover)(a:α)(u:Cloth β):
    let M:=terrain.gap (parentC L o) u.1; |Newt.tail d (fun y=> spring L Q (o+y,a) u) x| ≤
       (C*Real.exp (8*s)/(L.val:ℝ)^(1+d))*Real.exp (-s*M)*Real.exp (s/L.val*size x)*(1+size x:ℝ)^d := by
    have hf:=h.1; intro M; refine Newt.localized (E:=ℝ) (p:=fun y=> spring L Q (o+y,a) u) d (by positivity) (size x) ?_ x le_rfl
    intro l hh p he; refine (h.2 l hh.le o p a u).trans ?_
    rw [hh]; refine (mul_le_mul_of_nonneg_left (pack_clock L hp.le o (o+p) _ (c:=size x) ?v) (div_nonneg hf (by positivity))).trans_eq ?_
    case v=>
      show terrain.gap o (o+p)≤ size x; unfold terrain; simp only [add_sub_cancel_left]; exact_mod_cast he
    dsimp only [M]; ring
end stepCost

lemma crank_fee (G:Gauge)(k:ℝ)(hp:0<k){j t:ℕ}(hj:4≤j)(ht:4≤t):
     ∃ η C:ℝ,0<η∧0<C∧∀ (A:Levels G)(m N:ℕ), A.clock.kernel.penalty=k→A.clock.J m=t→A.clock.J (m+1)=j→
         Crank (shuttleM (gaugedA G (loose A m) (predictionA A N m))) (j-2) η C:=by
  obtain ⟨η,c,h,hc,hb⟩ :=advance_actual (G:=G) k hp hj ht
  refine ⟨η,c,h,hc,?_⟩; intro A m N he ha ht
  let P:=loose A m; let M:= predictionA A N m
  refine ⟨hc.le,?_⟩; intro l hl o x a u
  have hx:= hb A m N he ha ht l.reverse (by simpa only [List.length_reverse] using hl)
  have H: (advanceC P.L (gaugedA G P M) l.reverse).strip η (c/(P.L.val:ℝ)^(1+l.length)) := by
     rw [color_step]; refine coloration_paid _ _ _ (by positivity) ?_; simpa only [List.length_reverse] using hx
  let R:= advanceC P.L (gaugedA G P M) l.reverse
  rw [← profit _ (P.odd_side)]
  have hg : dragCup terrain η (c/(P.L.val:ℝ)^(1+l.length)) (shuttleM R):= matrix_width H (by positivity)
  have hv:= hg.2 ((panel P.L (Hooks G)).symm (o+x,a)) u
  have hl : ((panel P.L (Hooks G)).symm (o+x,a)).1=parentC P.L (o+x):= congr_arg Prod.fst (patchwork (o+x,a)); rw [hl] at hv
  exact hv
end YM.WilsonCoeffUV.Bank

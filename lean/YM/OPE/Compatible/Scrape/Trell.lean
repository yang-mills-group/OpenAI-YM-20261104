import YM.OPE.Compatible.Grid.Bookie
/-! # Every route prefix is itself that route. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Lattice Laurent MeasureTheory RG Wilson Flume Flume.Page Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{E X:Type*}{n:Side}{i k r m:ℕ}
lemma straightC (i:Axis)(d:ℤ)(l:ℕ) :∃ d':ℤ, (straight i d).take l=straight i d':=by
    by_cases hx:d<0; let k:=min l d.natAbs; refine ⟨-(k:ℤ),?_⟩
    · by_cases he:k=0
      · rw [he]; simp only [straight,List.take_replicate]; simp [← show k=min l d.natAbs from rfl,he]
      simp only [straight,List.take_replicate]; change List.replicate k _= List.replicate (-(k:ℤ)).natAbs _; simp [he,hx]; omega
    let k:=min l d.natAbs; refine ⟨k,?_⟩; unfold straight; rw [List.take_replicate]; change List.replicate k _= List.replicate (k:ℤ).natAbs _; simp [hx]
lemma RouteP (x:Cover)(l:List Axis)(z:ℕ)(he:l.Nodup):
      axisRoute 0 (stop 0 ((axisRoute 0 x l).take z)) l=(axisRoute 0 x l).take z∧ ∀ i:Axis,i∉ l→stop (0:Cover) ((axisRoute 0 x l).take z) i=0:=by
      induction l using List.reverseRecOn generalizing z with
      | nil=> simp [axisRoute,stop]
      | append_singleton l i H=>
          have ht : i ∉ l:=fun h=> (List.nodup_append.mp he).2.2 _ h _ (by simp) rfl; have hp:= (List.nodup_append.mp he).1; let A:= axisRoute 0 x l; let f:= straight i (x i); have hh(y:Cover): axisRoute 0 y (l++[i])= axisRoute 0 y l ++ straight i (y i):=by simp [axisRoute]
          rw [hh x]
          by_cases hv:z≤A.length
          · rw [List.take_append_of_le_length hv,hh]; obtain ⟨hQ,hz⟩:= H z hp; rw [show _=_ from hQ]; let u:=hz i ht; simp only [A,u,straight,Int.natAbs_zero,List.replicate_zero,List.append_nil]; exact ⟨True.intro,fun i hy=> hz _ (fun h=>hy (List.mem_append_left _ h))⟩
          obtain ⟨d,hd⟩:= straightC i (x i) (z-A.length); rw [List.take_append,List.take_of_length_le (Nat.le_of_not_ge hv),hd,stop_append,axisRoute_end 0 x (0:Cover) l hp, straight_stop] -- ordre
          let a:= fun j=> if j∈l then x j else (0:ℤ); let q:=a+d • (step i:Cover)
          simp only [Pi.zero_apply,sub_zero,zero_add]; change axisRoute 0 q (l++[i])= _ ∧∀ i',i'∉_ → q i'=0
          have hy (j)(hj:j∈l): q j=x j:=by simp [q,a,hj,show j≠i from fun h=>ht (h ▸ hj)]
          rw [hh q,show axisRoute 0 q l=axisRoute 0 x l from List.flatMap_congr (fun j h=> by rw [hy j h]),show q i=d from by simp[q,a,ht]]
          refine ⟨rfl,fun j hj=>?_⟩; simp only [List.mem_append,List.mem_singleton,not_or] at hj; simp [q,a,hj]
lemma pickC (p:Cover)(l:ℕ): carryP (stop 0 ((carryP p).take l))=(carryP p).take l:=
      (RouteP p (allAxes 1) l ((List.nodup_finRange _).map (1:Lattice.Order).injective)).1
abbrev incG (U:CoverConfig G) (x:Cover):G.El:= travel U 0 (carryP x)
def Scav (U:CoverConfig G):CoverConfig G:= Lattice.gauge (incG U) U
lemma pathPlate (U:CoverConfig G)(x:Cover)(r:ℕ):travel (Scav U) 0 ((carryP x).take r)=1:=by
     unfold Scav; rw [travel_gauge]; unfold incG; rw [pickC]; simp [carryP,travel] -- simp travel
lemma ringE (U:CoverConfig G)(i:Edge Cover): travel U 0 (ringO i)=Scav U i:=by
     unfold ringO; rw [travel_append,travel_append,stop_append,show stop 0 (carryP i.1)=i.1 from route_end ..,show stop i.1 _=i.1+step i.2 from rfl,show travel U (i.1+step i.2) _= (incG U (i.1+step i.2))⁻¹ from by
          have hp:=travel_reverse (carryP (i.1+step i.2)) U (0:Cover); rw[show stop 0 _=i.1+step i.2 from route_end ..] at hp; exact hp]; simp only [travel,mul_one];rfl
lemma CurU (U:CoverConfig G)(i:Edge Cover): indexS i (board U)=G.curvature (Scav U i):=by ext1 j; change G.curvature (travel U 0 (ringO (i.1,i.2))) j=_; rw [ringE]
lemma peeler (U:CoverConfig G)(x:Cover)(w:Walk)(t:ℝ)(h:∀ r:ℕ, travel (Scav U) x (w.take r)=1) : (pieces (t • board U) x w).sum=0:=by
     induction w generalizing x with
     | nil=> simp [pieces]
     | cons i w ih=>
          have hv:= h 1; rw [show List.take 1 _= [i] from rfl,travel,travel,mul_one] at hv; have hp: Scav U (i.used x)=1:=by unfold Step.read at hv; split at hv; exact inv_injective (by simpa only [inv_one] using hv : (Scav U (i.used x))⁻¹=(1:G.El)⁻¹); exact hv
          have he(k:ℕ):travel (Scav U) (x+i.vec) (w.take k)=1:=by
               have he:=h (k+1); rw [show List.take (k+1) _=i::w.take k from rfl, travel, hv,one_mul] at he; exact he
          have ht:indexS (i.used x) (t • board U)=0:=by rw [show indexS (i.used x) (t • board U)=t • indexS (i.used x) (board U) from rfl,CurU,hp,G.curvature_unit,smul_zero]
          rw [pieces,List.sum_cons,ih (x+i.vec) he,ht]; split <;> simp
lemma sourceU (U:CoverConfig G)(t:ℝ): risingO (t • board U)=t • board U:=by
      have h : candor (t • board U)=0:= by funext i; unfold candor bandC;rw [peeler ..,neg_zero]; rfl; exact pathPlate U i.1
      unfold risingO; rw[h,show mountain (0:fieldX G.ColorIndex)=0 from funext fun i=>sub_self (0:ℝ),add_zero]
end YM.OPE.Spells

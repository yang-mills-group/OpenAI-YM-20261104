import YM.WilsonCoeffUV.Ward.NoValue
/-!
# Leading and subleading Ward moments. No radial symmetry imposed at higher jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{t A:ℝ}{P: Canvas G} {e:ℕ}

-- orbit shifts from genuine center.
def tSign (s:Signed)(a:Axis):ℝ:= if s.flip a then -1 else 1
def drift (s:Signed)(i:Axis): Cover:= if s.flip i then -step (s.perm i) else 0
lemma color_shove (s:Signed)(z x:Cover)(i:Axis)(v:G.ColorIndex):
    tickW s z (stone (x,i) v)=stone (s.act x+z+drift s i,s.perm i) v:=by
    rw [tick_stone]; unfold drift; cases he:s.flip i <;> simp [he,ringS, Step.used,Step.rotate,posDir,affine, sub_eq_add_neg]

def Spin (K:Ten ℝ (YForest G) 2): Prop:= ∀ s z x,K (tickW s z ∘ x)= (∏ i,rimSign s (x i).2)* K x
def Medium (K:Ten ℝ (YForest G) 2): Prop := ∀ x y:Edge Cover,∃ k:ℝ,∀ i j:G.ColorIndex,K ![stone x i,stone y j]=if i=j then k else 0
lemma spin_has (h:swing P) : Spin (P e 2) := fun s z=> h s z e 2
lemma loyal_medium (h:leanTwo P): Medium (P e 2) := h e

variable {K:Ten ℝ (YForest G) 2}
def spill (s:Signed)(a b:Axis) : Equiv.Perm Cover:= s.actEquiv.toEquiv.trans (Equiv.addRight (drift s b-drift s a))
lemma shift_law (h:Spin K)(s:Signed)(u v:G.ColorIndex)(a b:Axis)(x:Cover):
    petals K (coord (s.perm a),u) (s.perm b) v (spill s a b x) = tSign s b*tSign s a*petals K (coord a,u) b v x:=by
    let i : Fin 2→ YForest G:=Fin.cons (stone (x,b) v) ![stone (0,a) u]
    have hx := h s (-drift s a) i
    have he : tickW s (-drift s a) ∘ i= Fin.cons (stone (spill s a b x,s.perm b) v) ![stone (0,s.perm a) u]:= by
      ext1 j
      fin_cases j
      · change tickW s _ (stone (x,b) v)=stone _ v; rw [color_shove]; change stone (_,_) v=stone (s.act x+(drift s b- drift s a),s.perm b) v; rw [sub_eq_add_neg, add_assoc,_root_.add_comm (-drift s a)]
      change tickW s _ (stone (0,a) u)= stone (0,s.perm a) u; rw [color_shove]; simp
    rw [he, Fin.prod_univ_two] at hx
    change K _= rimSign s (stone (x,b) v).2*rimSign s (stone (0,a) u).2*_ at hx
    rw [rim_stone,rim_stone] at hx; exact hx

lemma chalk_S (s:Signed)(k:Axis)(a b:Axis)(x): chalk (s.perm k) (spill s a b x)= tSign s k * chalk k x + chalk (s.perm k) (drift s b-drift s a):=by
    change ((s.act x+(drift s b-drift s a):Cover) (s.perm k):ℝ)=_; rw [Pi.add_apply,Int.cast_add,s.act_at]; unfold tSign chalk; split <;> simp
lemma rolledT (h:Spin K)(s:Signed)(u v:G.ColorIndex)(a b:Axis)(f:Cover→ℝ):
    tailor K (coord (s.perm a),u) (s.perm b) v f=tSign s b*tSign s a * tailor K (coord a,u) b v (f ∘ spill s a b) := by
    unfold tailor; rw [←tsum_mul_left,← (spill s a b).tsum_eq (fun x=>_)]
    exact tsum_congr fun x=> by rw [shift_law h]; simp only [Function.comp_apply]; ring
lemma broad_gain {f}(a:broad f)(c:ℝ): broad (c•f):= (broad.const c).mul a
lemma spin_chalk (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(s:Signed)(u v:G.ColorIndex)(a b k:Axis):
    tailor K (coord (s.perm a),u) (s.perm b) v (chalk (s.perm k))= tSign s b*tSign s a *(tSign s k)*tailor K (coord a,u) b v (chalk k):=by
    let c:=chalk (s.perm k) (drift s b-drift s a)
    rw [rolledT h]
    rw [show chalk (s.perm k) ∘ spill s a b=tSign s k • chalk k+c • (1:Cover→ℝ) from funext (fun x=>by rw [Function.comp_apply,chalk_S]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul, Pi.one_apply,mul_one]; rfl), tailor_add p hp _ _ _ (broad_gain (broad.chalk _) _) (broad_gain broad.one c),tailor_M,tailor_M,kail p hp w]; ring
lemma wick_white (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(i:Hooks G)(v:G.ColorIndex)(b k:Axis):
   tailor K i b v (chalk k)=0:= by
   let a:= axisEquiv.symm i.1; let s:Signed := ⟨Equiv.refl _,fun _=>true⟩
   have he:= spin_chalk h p hp w s i.2 v a b k
   simp [tSign,s,a,←coord_map] at he; linarith
lemma spin_squares (h:Spin K)(p:Amber terrain t A K)(hp:0<t)(w:∀ x c,windsL x c K=0)(s:Signed)(u v:G.ColorIndex)(a b k l:Axis):
    tailor K (coord (s.perm a),u) (s.perm b) v (chalk (s.perm k)*chalk (s.perm l))= tSign s b*tSign s a * tSign s k*tSign s l*tailor K (coord a,u) b v (chalk k*chalk l) := by
   let c (v:Axis):= chalk (s.perm v) (drift s b-drift s a)
   have he : (chalk (s.perm k)*chalk (s.perm l)) ∘ spill s a b=(tSign s k*tSign s l) • (chalk k*chalk l) + (c k*tSign s l) • chalk l +(c l*tSign s k) • chalk k +(c k*c l) • (1:Cover→ℝ):=by
     funext x; simp only [Function.comp_apply,Pi.mul_apply,chalk_S,Pi.add_apply,Pi.smul_apply]
     simp only [c,Pi.one_apply,smul_eq_mul]; ring
   have ht := broad_gain ((broad.chalk k).mul (broad.chalk l)) (tSign s k*tSign s l)
   have hu := broad_gain (broad.chalk l) (c k*tSign s l)
   have hh := broad_gain (broad.chalk k) (c l*tSign s k)
   rw [rolledT h,he, tailor_add p hp _ _ _ ((ht.add hu).add hh) (broad_gain broad.one _), tailor_add p hp _ _ _ (ht.add hu) hh, tailor_add p hp _ _ _ ht hu,tailor_M,tailor_M,tailor_M,tailor_M, wick_white h p hp w,wick_white h p hp w,kail p hp w]; ring

-- class scalar response
lemma liner (h:Medium K)(a b:Axis)(u v c:G.ColorIndex) (f:Cover→ℝ): tailor K (coord a,u) b v f=(if u=v then tailor K (coord a,c) b c f else 0):= by
    have hh (x:Cover): petals K (coord a,u) b v x= if u=v then petals K (coord a,c) b c x else 0:=by
      obtain ⟨r,hp⟩:= h (x,b) (0,a)
      unfold petals
      have he i j: K (Fin.cons (stone (x,b) i) ![(0,coord a,j)])= if i=j then r else 0:= hp i j
      rw [he,he]; by_cases he:u=v<;> simp [*,eq_comm]
    unfold tailor; split <;> rename_i he
    · simp_rw [hh, if_pos he]
    simp_rw [hh,if_neg he, mul_zero]; simp
lemma fuel_twin {a i b j : Axis}(h:a ≠ i)(e:b ≠ j) : ∃ f:Equiv.Perm Axis, f a=b ∧ f i=j := by
   let u:=Equiv.swap a b; have H:u i≠ b:= fun he=> h (u.injective (by rw [he]; exact Equiv.swap_apply_left ..))
   refine ⟨u.trans (Equiv.swap (u i) j), ?_,by simp⟩
   rw [Equiv.trans_apply,show u a=b from Equiv.swap_apply_left ..,Equiv.swap_apply_of_ne_of_ne (Ne.symm H) e]

lemma axle (p:Amber terrain t A K)(hp:0<t)(h:Spin K)(w:∀ x c,windsL x c K=0)(u:G.ColorIndex)(k:Axis){v:Hooks G} : tailor K v k u (chalk k*chalk k)=0:= by
    set d:= chalk k; have hg:=broad.chalk k
    have he:= jets_null p hp w v u (d*d*d) ((hg.mul hg).mul hg)
    have ht j (hh:j≠k): nextV j (d*d*d)=0:= by
       funext x; simp [nextV,d,chalk_inc,hh]
    rw [Finset.sum_eq_single k] at he
    · rw [show nextV k (d*d*d)=(3:ℝ) • (d*d)+(3:ℝ) • d +1 from ?_,tailor_add p hp _ _ _ ((broad_gain (hg.mul hg) _).add (broad_gain hg _)) broad.one, tailor_add p hp _ _ _ (broad_gain (hg.mul hg) _) (broad_gain hg _), tailor_M,tailor_M,kail p hp w] at he
      · rw [wick_white h p hp w] at he; linarith
      funext x; simp [nextV,d,chalk_inc]; ring
    · intro j _ hv; rw [ht _ hv, tailor_zero]
    simp
lemma cornerM (p:Amber terrain t A K)(hp:0<t)(h:Spin K)(w:∀ x c,windsL x c K=0)(u:G.ColorIndex)(v:Hooks G)(a k:Axis)(hw:a≠k):
    tailor K v a u (chalk k*chalk k)+2*tailor K v k u (chalk a*chalk k)=0:=by
    set D:=chalk a; set T:=chalk k
    let ht: broad (D*T*T):= ((broad.chalk a).mul (broad.chalk k)).mul (broad.chalk k)
    have he:= jets_null p hp w v u _ ht
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), Finset.sum_eq_single k] at he
    · rw [show nextV a (D*T*T)=T*T from ?_, show nextV k (D*T*T)=(2:ℝ) • (D*T)+D from ?_,tailor_add p hp _ _ _ (broad_gain ((broad.chalk a).mul (broad.chalk k)) _) (broad.chalk a),tailor_M] at he
      · unfold T at he; rw [wick_white h p hp w] at he; simpa using he
      all_goals funext x; simp [nextV,D,T,chalk_inc,hw,Ne.symm hw]; ring
    · intro j hj h'; have he:j≠a:= (Finset.mem_erase.mp hj).1; rw [show nextV j _=0 from ?_,tailor_zero]; funext x; simp [nextV,D,T,chalk_inc,he,h']
    simp [Ne.symm hw]

end YM.WilsonCoeffUV.Bank

import YM.AveragedStep.Stokes.Rays
import YM.Push.STATIONARY_UNIFORM.FrameMin
import YM.Pressure.Macro
import YM.Branch.Predict
/-! Local torus prediction, price curvature *along the physical tags*. Keep
path connector and its endpoints. Use a proof-only gauge on the COVER to
price through switches. Constants at this milestone post-L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.Loops
open Lattice Wilson Function RG Push.Uniform Pressure
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}

/-- Literal finite curvature invoice on the universal cover. Doesn't
matter that faces, tags or anchors collide after projection. -/
def Bought (X : CoverConfig G → G.El) := ∃ (l : List (Face ℤ))(C:ℝ),
  0≤C ∧ ∀ U,G.chord (X U) ≤ C*bill U l
lemma bought_inv {X : CoverConfig G → G.El}(h:Bought X):Bought (fun x=>(X x)⁻¹):=by
  obtain ⟨l,C,hC,H⟩:=h; exact ⟨l,C,hC,fun U=> (G.chord_inv ..).le.trans (H _)⟩
lemma bought_mul {X Y : CoverConfig G → G.El}(h:Bought X)(k:Bought Y):Bought (fun x=>X x*Y x):=by
  obtain ⟨l,C,hC,H⟩:=h; obtain ⟨p,D,hD,J⟩:=k; refine ⟨l++p,max C D,hC.trans (le_max_left ..),fun U=>?_⟩
  rw [bill_append, mul_add]
  exact (G.chord_triangle (X U) _).trans (add_le_add
    ((H U).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (bill_pos ..)))
    ((J U).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (bill_pos ..))))
lemma together {I:Type} [Fintype I] (X:I→CoverConfig G→ G.El)(h:∀ i,Bought (X i)):
    ∃ (l:List (Face ℤ))(C:ℝ),0≤C ∧ ∀ (i:I)(U:CoverConfig G),G.chord (X i U) ≤ C*bill U l:=by
  suffices hw:∀(s:Finset I),∃ (l:List (Face ℤ))(C:ℝ),0≤C ∧∀ i∈s,∀ U,G.chord (X i U) ≤ C*bill U l by
    obtain ⟨l,C,hC,H⟩:=hw Finset.univ; exact ⟨l,C,hC,fun i=> H i (Finset.mem_univ _)⟩
  intro s; induction s using Finset.induction_on with
  | empty=> exact ⟨[],0,le_rfl,by simp⟩
  | insert i s _ ih=>
    obtain ⟨l,C,hC,H⟩:=h i; obtain ⟨q,D,hD,T⟩:=ih; refine ⟨l++q,max C D,hC.trans (le_max_left ..),?_⟩
    intro j hj U; rw [bill_append]; rcases Finset.mem_insert.mp hj with rfl|h
    · exact (H U).trans (mul_le_mul (le_max_left ..) (le_add_of_nonneg_right (bill_pos ..))
                       (bill_pos ..) (hC.trans (le_max_left ..)))
    exact (T j h U).trans (mul_le_mul (le_max_right ..) (le_add_of_nonneg_left (bill_pos ..))
                       (bill_pos ..) (hC.trans (le_max_left ..)))

def tent (U:CoverConfig G)(x:Cover):G.El:=travel U 0 (route 0 x 1)
@[simp] lemma tent_root (U:CoverConfig G):tent U 0=1:=by simp [tent,travel]
lemma peal (x : Cover)(w:Walk):Bought fun U:CoverConfig G=>travel (Lattice.gauge (tent U) U) x w:=by
  let y:=stop x w
  let p:= fun z:Cover=>route 0 z 1
  let q:=p x ++ w ++ Lattice.reverse (p y)
  have he(v):stop (0:Cover) (p v)=v:=route_end ..
  have hv : stop (0:Cover) q=0:=by
    unfold q; simp_rw [stop_append,he]
    have h:=reverse_stop (p y) (0:Cover); rwa [he y] at h
  obtain ⟨l,_,H⟩:=closed q hv (0:Cover)
  refine ⟨l,1,zero_le_one,fun U=>?_⟩
  have ht:=H G U; simp_rw [q,travel_append, stop_append,he] at ht
  have hf:=travel_reverse (p y) U (0:Cover); rw [he] at hf
  rw [show stop x w=y from rfl,hf] at ht
  rw [one_mul]; simpa only [p,tent,travel_gauge, y] using! ht

lemma travel_shift (U:CoverConfig G)(x y:Cover)(w:Walk):travel (translate x U) y w=travel U (y+x) w:=by
  induction w generalizing y with
  | nil=>rfl
  | cons a w ih=>
    rw [travel,travel,ih,show y+a.vec+x=y+x+a.vec by abel]; apply congr_arg (· * _)
    rcases a with ⟨i,h|h⟩; rfl
    change (U (y-step i+x,i))⁻¹=(U (y+x-step i,i))⁻¹
    rw [sub_add_eq_add_sub]

/- all paths/forks inside the predictor; can price post-tag when wrapping too. -/
variable (P:Patch) (K:KernelChoices)
lemma frame_bought (x:Cover)(t:P.FrameTag)(a:P.Points):Bought fun U:CoverConfig G=>P.frame K (translate x (Lattice.gauge (tent U) U)) t a:=by
  let F:=fun (i:P.Points×P.Points×Lattice.Order) (U:CoverConfig G)=> travel (translate x (Lattice.gauge (tent U) U)) i.1.val (route i.1.val i.2.1.val i.2.2)
  obtain ⟨l,C,hC,H⟩:=together F fun i=>by unfold F; simp_rw [travel_shift]; apply peal
  refine ⟨l,(alignCost P+2)*C,by have ht:=align_pos P; positivity,fun U=>?_⟩
  let Q:=translate x (Lattice.gauge (tent U) U)
  let r:=C*bill U l
  have hr:0≤r:=mul_nonneg hC (bill_pos ..)
  have hh:ClosePaths P Q r:=fun a b q=> H (a,b,q) U
  change G.chord (P.frame K Q t a) ≤ _
  unfold Patch.frame; split
  · apply (cluster_root P (P.min_exists Q).choose_spec hh a).trans
    rw [mul_assoc]; change _ ≤ _*r; gcongr; linarith
  apply (G.chord_triangle _ _).trans; rw [G.chord_inv]
  apply (add_le_add (hh t.1 P.center t.2) (hh t.1 a t.2)).trans
  rw [mul_assoc]; change r+r ≤ _*r; nlinarith only [mul_nonneg (align_pos P).le hr]

omit P K in
lemma length_stop (m:ℕ)(i:Axis)(x:Cover): stop x (List.replicate m (posDir i))= x+m • step i:=by
  induction m generalizing x with
  | zero=>simp [stop]
  | succ m ih=> rw [List.replicate_succ,stop,ih,succ_nsmul,Step.vec_pos]; abel

def coverY (t u:P.FrameTag) (i:Axis)(U:CoverConfig G):P.Connector G:= fun z=>
  P.frame K U t z*travel U z.val (List.replicate P.L.val (posDir i))*(P.frame K (translate (P.L.val • step i) U) u z)⁻¹
def coverQ(t u:P.FrameTag)(b:P.Points)(i:Axis)(U:CoverConfig G):= P.predict K (coverY P K t u i U) b
lemma q_bought (t u:P.FrameTag)(b:P.Points)(i:Axis):Bought fun U:CoverConfig G=> coverQ P K t u b i (Lattice.gauge (tent U) U):=by
  let V:=fun U:CoverConfig G=> Lattice.gauge (tent U) U
  let X:=fun z (U:CoverConfig G)=>coverY P K t u i (V U) z
  have he:∀ z,Bought (X z):=by
    intro z
    have hr : Bought (fun U:CoverConfig G=>P.frame K (V U) t z):=by
      simpa only [V,show ∀ x:CoverConfig G,translate 0 x=x by intro x; unfold translate; simp] using frame_bought (G:=G) P K 0 t z
    exact bought_mul (bought_mul hr (peal _ _)) (bought_inv (frame_bought P K _ u z))
  obtain ⟨l,C,hC,H⟩:=together X he
  let M:=2*max 1 K.predictor_cut⁻¹
  have hM:0≤M:=by unfold M; positivity
  refine ⟨l,M*C,mul_nonneg hM hC,fun U=>?_⟩
  have ht:=price_query P K (coverY P K t u i (V U)) b (1:G.El) 1
  simp only [inv_one,one_mul,mul_one] at ht
  refine ht.trans (le_trans (b:=M*(∑ j,P.weight j*(C*bill U l))) ?_ ?_)
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (H j U) (P.weight_nonneg _))) hM
  rw [← Finset.sum_mul, P.weight_sum,one_mul]; exact le_of_eq (by unfold M; ring)

lemma q_changes (h:P.Branches K G)(t u:P.FrameTag)(b:P.Points)(i:Axis)
    (U:CoverConfig G)(k:Cover→G.El):
    let x:=P.L.val • step i
    coverQ P K t u b i (Lattice.gauge k U) = k 0 * coverQ P K t u b i U * (k x)⁻¹ := by
  intro x
  let v:=fun z=> k (z+x)
  have he:translate x (Lattice.gauge k U)=Lattice.gauge v (translate x U):=by
    funext e; simp only [v,translate,Lattice.gauge]; rw [add_right_comm e.1]
  unfold coverQ
  rw [show coverY P K t u i (Lattice.gauge k U)=(fun j=>k 0 * coverY P K t u i U j *(k x)⁻¹) from ?_,
    (P.bond_gauge (h:=h) ..).2]
  funext z; unfold coverY; rw [travel_gauge,length_stop]; change _*(_*_*_) * (P.frame K (translate x _) _ _)⁻¹ = _
  rw [(P.frame_gauged h ..).2,he,(P.frame_gauged h ..).2]
  change k (0:Cover)*_*_*(_*_*_) *(k ((0:Cover)+x)*_*(k (z.val+x))⁻¹)⁻¹=_
  rw [zero_add]; unfold x; group
lemma straight_difference (h:P.Branches K G)(t u:P.FrameTag)(b:P.Points)(i:Axis):
    Bought fun U:CoverConfig G=>coverQ P K t u b i U*(travel U 0 (List.replicate P.L.val (posDir i)))⁻¹:=by
  -- don't even prove ray along axis; both to same stop.
  let V:=fun U:CoverConfig G=>Lattice.gauge (tent U) U
  let X:=fun U:CoverConfig G=> coverQ P K t u b i (V U)*(travel (V U) 0 (List.replicate P.L.val (posDir i)))⁻¹
  have he:Bought X:=bought_mul (q_bought P K t u b i) (bought_inv (peal 0 _))
  convert he using 2
  unfold X V; rw [q_changes P K h,travel_gauge,length_stop,zero_add,tent_root,one_mul,one_mul]; group
end YM.AveragedStep.Loops

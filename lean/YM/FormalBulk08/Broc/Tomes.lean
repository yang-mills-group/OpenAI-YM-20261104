import YM.FormalBulk08.Broc.Cave

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{r t m e E:ℕ}{A K σ η:ℝ}

structure LeafD (G:Gauge) where
    u:ℕ
    t:ℕ
    field:Skin G (t+1)
    arr:Pot G
structure Honest (P:LeafD G)(E:ℕ)(σ A:ℝ):Prop where
    high:P.u≤E
    size:P.t ≤ P.u
    parity:(P.t+2)%2=P.u%2
    wall:AtomWall (issue P.field) σ A
    bumps: Bumps G (P.t+1) (0<P.u) P.field
    paths: Freeze P.arr (issue P.field) P.u
    bill: Fits P.arr E σ A

def binding (P:List (LeafD G)):Pot G:= (P.map LeafD.arr).sum
@[simp] lemma binding_nil: binding (G:=G) []=0:=by simp [binding]
@[simp] lemma binding_one (a:LeafD G)(P:List (LeafD G)): binding (a::P)=a.arr+binding P:=by simp [binding]
@[simp] lemma binding_two (P Q:List (LeafD G)): binding (P++Q)=binding P+binding Q:=by simp [binding]
-- collect warms. h layout
variable {P Q:List (LeafD G)} {p:LeafD G}
lemma vivid_zero : Vivid (0: Pot G):= ⟨fun _ _=>up_zero _,fun _ _=> agate_zero _,by simp⟩
lemma zero_float : FloatK (0:Pot G):= { vivid_zero with
   fare:= fun i r=>⟨1,0,one_pos,bail_void ..⟩
   civic:= fun n=> by
      intro s x I inst a b k _ _ _ _ _ _ _; rw [show stone (0:Pot G) n=0 by ext1 i;simp [sow_coeff,sow,cum_zero],map_zero,map_zero] }
lemma zero_fit (E:ℕ)(h:0≤A):Fits (0:Pot G) E σ A:=⟨h,fun _ _ _=> (bail_void ..).mono h⟩
structure Edition (P:List (LeafD G))(E:ℕ)(σ A:ℝ):Prop where
    honest:∀ a ∈ P,Honest a E σ A
    fiscal:Fits (binding P) E σ A
lemma Honest.mono (h:Honest p E σ A)(ht:η≤σ)(hv:A≤K): Honest p E η K := {h with wall:=h.wall.mono ht hv,bill:=h.bill.mono ht hv}
lemma Edition.mono (h:Edition P E σ A)(ht:η≤σ)(hv:A≤K): Edition P E η K := ⟨fun _ ha=> (h.honest _ ha).mono ht hv,h.fiscal.mono ht hv⟩
lemma no_edition (h:0≤A): Edition (G:=G) [] E σ A:=⟨by simp,by rw [binding_nil]; apply zero_fit _ h⟩
lemma by_edition (h:Honest p E σ A)(H:Edition P E σ K): Edition (p::P) E σ (A+K):= ⟨fun j hj=> by
   rcases List.mem_cons.mp hj with rfl|hp; exact h.mono le_rfl (le_add_of_nonneg_right H.fiscal.money);exact (H.honest _ hp).mono le_rfl (le_add_of_nonneg_left h.bill.money),by rw [binding_one]; exact h.bill.add H.fiscal⟩
lemma with_edition (h:Edition P E σ A)(u:Edition Q E σ K): Edition (P++Q) E σ (A+K):= by
    refine ⟨fun i hi=>?_,by rw [binding_two]; exact h.fiscal.add u.fiscal⟩; rcases List.mem_append.mp hi with h'|h'; exact (h.honest _ h').mono le_rfl (le_add_of_nonneg_right u.fiscal.money);exact (u.honest _ h').mono le_rfl (le_add_of_nonneg_left h.fiscal.money)
lemma warm_binding (h:∀ a∈P,Honest a E σ A): FloatK (binding P):= by
    induction P with
    | nil=> rw [binding_nil]; exact zero_float
    | cons a P ih=> rw [binding_one]; exact float_plus (h a (List.mem_cons_self ..)).paths.toFloatK (ih fun i hi=> h i (List.mem_cons_of_mem _ hi))
lemma binding_root (v: binding P e r ≠0): ∃ a∈P, a.arr e r≠0:= by
    induction P with
    | nil=> exact False.elim (by simp [binding] at v)
    | cons a P ih=>
        by_cases hp: a.arr e r=0
        · rw [binding_one,Pi.add_apply,Pi.add_apply,hp,zero_add] at v; obtain ⟨b,h,H⟩:= ih v; exact ⟨b,List.mem_cons_of_mem _ h,H⟩
        exact ⟨_,List.mem_cons_self ..,hp⟩
lemma book_mountain (h:∀ a∈P,Honest a E σ A) : stone (binding P) n= (P.map (fun a=> mountain (issue a.field) n a.u)).sum:= by
    induction P with
    | nil=> ext1 i; simp [binding,sow,cum_zero]
    | cons a P ih=>
      let q:= h a (List.mem_cons_self ..); have ht:∀ b∈P,Honest b E σ A:= fun b hb=> h b (List.mem_cons_of_mem _ hb); have he : stone (a.arr+binding P) n= stone a.arr n+ stone (binding P) n:= by
          ext1 e;rw [map_add]; simp_rw [sow_coeff,sow]; rw [←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> ?_; obtain ⟨η,B,h1,H1⟩:=q.paths.fare e (i+1); obtain ⟨δ,D,h2,H2⟩:= (warm_binding ht).fare e (i+1); rw [←map_add]; exact congr_arg _ (cum_plus 0 n h1.le h2.le H1 H2)
      rw [binding_one,he,q.paths.mountain n, ih ht]; rfl
structure Temper (T:Pot G)(E:ℕ):Prop where
    up:∀ e≤E,∀ i,Up (T e i)
    ports:∀ e≤E,∀ i, Agate (T e i)
    valence:∀ e≤E,∀ i,T e i≠0 → 0 < i ∧ i≤e+2 ∧ i%2=e%2
    rite:∀ n, Charter (stone T n) E
variable {T S:Pot G}
lemma tome_in {P Q : Pap (wire G n)}(h:Charter P E)(ht:Through E P Q): Charter Q E:= fun a x i _ u v k hu hv hU hV hk hz hx=> Through.trans (Through.symm (Through.change_congr (insertAt ℝ (motor u)) ht)) ((h a x i u v k hu hv hU hV hk hz hx).trans (Through.change_congr (insertAt ℝ (motor v)) ht))
lemma charter_cap {p:Pap (wire G n)}(h:Civic p)(E): Charter p E:= by intro s x i inst u v k hu hv hU hV hk hz ht; rw [h _ _ _ _ _ _ hu hv hU hV hk hz ht]
lemma float_temp (h: FloatK T)(E): Temper T E:= ⟨fun e _=>h.civil e,fun e _=> h.agate e,fun e _=>h.valence e,fun n=> charter_cap (h.civic n) E⟩
lemma temper_less (H: Temper T E)(p:Temper S E)(b:Fits T E σ A)(h:Fits S E η K)(hs:0≤σ)(hη:0≤η): Temper (T-S) E:= by
   refine ⟨fun i a j=> Up.sub (H.up i a j) (p.up i a j),fun i a j=> (H.ports i a j).sub (p.ports i a j),fun i a j ht=> ?_,fun n=>?_⟩
   · by_cases he:T i j=0
     · refine p.valence i a j (fun h=> ht ?_); rw [Pi.sub_apply,Pi.sub_apply,he,h,sub_zero]
     exact H.valence i a j he
   refine tome_in ?_ (shed_stamp hs hη b h).symm
   intro s x i inst u v k hu hv hU hV hk hz ht; simp_rw [map_sub]; apply (H.rite n s x i u v k hu hv hU hV hk hz ht).sub (p.rite n s x i u v k hu hv hU hV hk hz ht)
end YM.FormalBulk08.Broc

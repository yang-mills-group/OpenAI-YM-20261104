import YM.XSpace.Offsite

/-!
# Position-estimate on the Dawn/Dusk (period/cover) pair of covariances
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Comets
open Function Set Lattice RG Wilson Source Source.Drops Next.Rank.Normal Contraction Chart2 Finsupp JetGauge Legs MvPolynomial Feynman Filter Outline Outline.Given
open Sail (reach cover gd)
open scoped Topology BigOperators
variable {G: Gauge}{R:Period}{Z:Type*}
def Tall (R:Period)(x:Cover):Prop:= R.side.val ≤16*pdist (wrap R.side (x+x))
def budget (R:Period)(r:ℕ):ℝ:= (1+(r:ℝ))/R.side.val
lemma budget_pos (R:Period)(r:ℕ):0<budget R r:=by unfold budget; positivity [Bloch.side_pos R.side]
lemma night_move (p:Bone G ℤ)(x:Cover): (dusk G).burn x p = ((p.1.1+x,p.1.2),p.2):= by obtain ⟨⟨b,c⟩,a⟩:=p; simp only [dusk,Given.burn,Given.points,Chart.shift,Chart.atop,Chart.lug,Chart.roll, Chart.move, Prod.map_apply, Function.comp_apply, id_eq, add_zero]
lemma dawn_move (p:Bone G ℤ)(x:Cover)(R:Period): (dawn G R).burn (wrap R.side x) p= ((wrap R.side (p.1.1+x),p.1.2),p.2):= by change ((wrap R.side p.1.1+_,_),_)=_; rw [map_add]; rfl
lemma length_pay {r:ℕ}(a b x y o:Cover)(h:reach (x-o)≤r)(h':reach (y-o)≤r): reach (a+x - (b+y)) ≤ reach a + r+reach b+r:=by
  have he : a+x-(b+y)=a+(x-o)+(-(b+(y-o))) :=by abel
  rw [he]; apply (Sail.tree ..).trans; rw [Sail.reach_neg]; apply (Nat.add_le_add ((Sail.tree ..).trans (add_le_add_right h _)) ((Sail.tree ..).trans (add_le_add_right h' _))).trans_eq (by omega)
lemma adjustment {r:ℕ}(a x y o:Cover)(h:reach (x-o)≤r)(h':reach (y-o)≤r) : reach (a+x+y-(o+o)) ≤ reach a + r+r:=by rw [show a+x+y-(o+o)=a+(x-o)+(y-o) by abel]; apply (Sail.tree ..).trans; gcongr; exacts [(Sail.tree ..).trans (by gcongr)]
lemma branch_calc {r:ℕ}(a x y o:Cover)(h:reach (x-o)≤r)(h':reach (y-o)≤r)(b:Tall R o) :
    saving (pdist (wrap R.side (a+x+y))) ≤ (reach a+(1+(r:ℝ)) + r)*16 /R.side.val:=by
  unfold Tall at b; let A:=pdist (wrap R.side (a+x+y)); let c:=reach a+r+r; let B:=pdist (wrap R.side (o+o)); have hC:B≤ A+c:=by
    unfold B; rw [show o+o=(a+x+y)+( -(a+x+y-(o+o))) by abel, map_add,map_neg]; apply (pdist_triangle ..).trans; rw [pdist_neg]; exact add_le_add (_root_.le_refl A) ((pc_cast ..).trans (adjustment a x y o h h'))
  have he : saving B ≤16/(R.side.val:ℝ):=by
    have h : 0 < (R.side.val:ℝ):=Bloch.side_pos _; have hb : (R.side.val:ℝ)≤16*B:=by exact_mod_cast b
    unfold saving; field_simp; linarith
  apply (saving_fee hC).trans; apply (mul_le_mul_of_nonneg_left he (by positivity : 0≤1+(c:ℝ))).trans_eq; unfold c; push_cast; ring

lemma general_G0 {n : Side} (z:Cover): Sail.beam [] n (wrap n z)= gd n (wrap n z):=rfl
lemma latch (i j:Bone G ℤ): ∃ C:ℝ,0≤C∧∀ R:Period,∀ o:Cover, Tall R o →∀ r:ℕ,∀ x y:Cover, reach (x-o)≤r → reach (y-o)≤r→
    ‖(dawn G R).grant.cov ((dawn G R).burn (wrap R.side x) i) ((dawn G R).burn (wrap R.side y) j) - (dusk G).grant.cov ((dusk G).burn x i) ((dusk G).burn y j)‖≤ C * budget R r:=by
  set a:=j.1.1-i.1.1; set b:=j.1.1+i.1.1+step i.1.2; obtain ⟨C,hC,H⟩:= Sail.continuity_cost []; obtain ⟨D,hD,K⟩:= Sail.seam []
  let q:ℕ:= Sail.reach j.1.1+ Sail.reach i.1.1+ Sail.reach b+2
  refine ⟨64*(C+D)*(1+(q:ℝ)),by positivity,fun R o hx r x y hv hy=>?_⟩
  let n:=R.side; have hn:=Bloch.side_pos n
  let c:Cover:=j.1.1+y-(i.1.1+x); let d:Cover:=b+x+y
  have hc: reach c ≤ q+2*r:=by have p:=length_pay j.1.1 i.1.1 y x o hy hv; unfold q c; omega
  set S:=saving (pdist (wrap n d)); have hs : S≤ (reach b+(1+(r:ℝ))+r)*16/n.val:= branch_calc (R:=R) b x y o hv hy hx
  rw [paired (R:=R),dawn_move, dawn_move, night_move, night_move]
  simp only [coal,mirror, R.reflect_axis]; unfold dusk duskCov; dsimp only [coal]; simp only [R.reflect_base]
  split_ifs with h
  · have he1 : wrap R.side (j.1.1+y)-wrap R.side (i.1.1+x)=wrap R.side c:=by unfold c; rw [map_sub]
    have he2 : wrap R.side (j.1.1+y) - (-(wrap R.side (i.1.1+x)+step i.1.2))= wrap R.side d:=by unfold d b; simp only [map_add,wrap_step]; abel
    rw [he1,he2,sub_right_comm, ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs]; apply (abs_sub ..).trans
    let z:=wrap n d
    have hp: |gd n z| ≤ D * (S + (n.val:ℝ)⁻¹) := (K n z).trans (mul_le_mul_of_nonneg_left (add_le_add_left ((Sail.carry_weight (pdist z) (show 1≤2+ ([]:List Axis).length by simp)).trans_eq (pow_one _)) _) hD.le)
    apply le_trans (add_le_add (H n c) hp);
    calc _ ≤ C*(1+(↑(q+2*r):ℝ))/n.val + D*((reach b+(1+(r:ℝ))+r)*16/n.val +(n.val:ℝ)⁻¹):=by gcongr
         _ ≤ _ := by change _ ≤ 64*(C+D)*(1+q)*((1+(r:ℝ))/n.val); push_cast [q]; field_simp; rw [← sub_nonneg]; ring_nf; positivity
  · simp [budget_pos]; positivity

def Region (Z: Type*) (p q: Period → (Z→Cover)→ℂ): Prop:=
 (∃ C:ℝ,0≤C∧∀ R:Period,∀ o: Cover,Tall R o→∀ r:ℕ,∀ x: Z→Cover,(∀ i,reach (x i-o)≤r)→‖p R x-q R x‖≤C*budget R r)∧
 (∃ C:ℝ,0≤C∧∀ R x, ‖p R x‖≤C)∧ (∃ C:ℝ,0≤C∧∀ R x,‖q R x‖≤C)
namespace Region
variable {p q v w : Period → (Z→Cover)→ℂ} (h:Region Z p q) (g:Region Z v w)
lemma const (Z:Type*)(x:ℂ): Region Z (fun _ _=>x) (fun _ _=>x):= ⟨⟨0,by simp,by intros; simp⟩,⟨‖x‖,norm_nonneg _,fun _ _=>le_rfl⟩,⟨‖x‖,norm_nonneg _,fun _ _=> le_rfl⟩⟩
include h g
lemma plus : Region Z (p+v) (q+w):=by
  obtain ⟨⟨C,hC,H⟩,⟨A,hA,F⟩,⟨B,hB,S⟩⟩:=h; obtain ⟨⟨c,hc,h⟩,⟨a,ha,P⟩,⟨b,hb,s⟩⟩:=g
  refine ⟨⟨C+c,by positivity, fun R o he r x hp=>?_⟩,⟨A+a,by positivity,fun R x=> (norm_add_le ..).trans (add_le_add (F R x) (P R x))⟩,⟨B+b,by positivity,fun R x=> (norm_add_le ..).trans (add_le_add (S R x) (s R x))⟩⟩
  simp only [Pi.add_apply]; rw [show _+_ -(q R x+_) = (p R x-q R x)+(v R x-w R x) by abel,_root_.add_mul]; exact (norm_add_le ..).trans (add_le_add (H R o he r x hp) (h R o he r x hp))
lemma mul : Region Z (p*v) (q*w):=by
  obtain ⟨⟨C,hC,H⟩,⟨A,hA,F⟩,⟨B,hB,S⟩⟩:=h; obtain ⟨⟨c,hc,h⟩,⟨a,ha,P⟩,⟨b,hb,s⟩⟩:=g
  refine ⟨⟨a*C+B*c,by positivity, fun R o he r x hp=>?_⟩,⟨A*a,by positivity,fun R x=>?_⟩,⟨B*b,by positivity,fun R x=>?_⟩⟩ <;> simp only [Pi.mul_apply]
  · rw [show _*_ -q R x*_=v R x*(p R x-q R x)+q R x*(v R x-w R x) by ring,_root_.add_mul,_root_.mul_assoc,_root_.mul_assoc B]; apply (norm_add_le ..).trans; simp_rw [norm_mul]; exact add_le_add (mul_le_mul (P ..) (H _ _ he _ _ hp) (norm_nonneg _) ha) (mul_le_mul (S ..) (h _ _ he _ _ hp) (norm_nonneg _) hB)
  · rw [norm_mul]; exact mul_le_mul (F ..) (P ..) (norm_nonneg _) hA
  rw [norm_mul]; exact mul_le_mul (S ..) (s ..) (norm_nonneg _) hB
omit h g
lemma sum {V:Type*}(s:Finset V)(p q:V→Period→(Z→Cover)→ℂ)(h:∀ i∈s,Region Z (p i) (q i)): Region Z (fun R x=>∑ i∈s,p i R x) (fun R x=>∑ i∈s,q i R x):=by
  classical induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact const Z _
  | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).plus (ih fun j hj=> h j (by simp [hj]))
end Region

-- multiple glyph Estimate
section
variable {V W: Type*} (K L : Period → (Z→Cover)→JetGauge.Cov V) (h:∀ i j, Region Z (fun R x=>(K R x).cov i j) (fun R x=>(L R x).cov i j))
include h
lemma head (u:W→V)(a:Finset W): Region Z (fun R x=>blend (K R x) 0 (glyphs u a)) (fun R x=>blend (L R x) 0 (glyphs u a)):= by
  classical
  induction a using Finset.strongInduction with
  | H a ih=>
    by_cases p:a=∅; subst a; simp [glyphs]; exact Region.const ..
    obtain ⟨j,hj⟩:= Finset.nonempty_iff_ne_empty.mpr p
    rw [show a=insert j (a.erase j) from (Finset.insert_erase hj).symm]; simp_rw [spring _ _ _ _ (Finset.notMem_erase _ _),Pi.zero_apply,zero_mul,zero_add]; exact Region.sum _ _ _ (fun k _=> (h (u j) (u k)).mul (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) (Finset.erase_ssubset hj))))
lemma rest (p:poly V): Region Z (fun R x=>blend (K R x) 0 p) (fun R x=>blend (L R x) 0 p):=by
  classical
  suffices H : ∀ m c, Region Z (fun R x=>blend (K R x) 0 (monomial m c)) (fun R x=>blend (L R x) 0 (monomial m c)) by rw [p.as_sum]; simp_rw [map_sum]; exact Region.sum _ _ _ (fun i _=> H ..)
  intro m c; let I:=(i : m.support) × Fin (m i.val); let a (x:I):=x.1.val
  have he: monomial m (R:=ℂ) c=c • glyphs a Finset.univ:=by rw [monomial_eq,← C_mul']; congr 1; simp [glyphs,I,a,Finsupp.prod,Fintype.prod_sigma]; apply Eq.symm; rw [Finset.prod_attach _ (fun i=> MvPolynomial.X (R:=ℂ) i ^ m i), monomial_eq,map_one,one_mul]; rfl
  rw [he]; simp_rw [map_smul]; exact (Region.const Z c).mul (head K L h a Finset.univ)
end

variable {S:Type*} [AddCommGroup S][One S]
def sign (g: Given G S)(z:Z→Four S) : JetGauge.Cov (Z× Bone G ℤ):= scope (fun i=>single (jump g z i) 1) g.grant
-- convoy may call from both period and cover even without near
lemma same_motor (g: Given G S)(z:Z→Four S) (p:Shadow) : blend g.grant 0 (motor g z p)=blend (sign g z) 0 p:=by rw [motor,labelled, wets]; rw [show (sign g z) = _ from rfl]; congr 2; first | rfl | (ext x; simp [reads])
lemma arc (p:Shadow (G:=G) (Z:=Z)): Region Z (fun R z=> E (dawn G R).grant (motor (dawn G R) (wrap _ ∘ z) p)) (fun _ z=> E (dusk G).grant (motor (dusk G) z p)):=by
  simp_rw [E,same_motor]; apply rest; intro i j
  unfold sign; simp_rw [match_name]; obtain ⟨C,hC,H⟩:= latch i.2 j.2; obtain ⟨A,hA,M⟩:= (dawning G).every; obtain ⟨B,hB,N⟩:= (night G).every
  exact ⟨⟨C,hC,fun R o he r x hx=> H R o he r (x i.1) (x j.1) (hx _) (hx _)⟩,⟨A,hA.le,fun R x=>M R _ _⟩,⟨B,hB.le,fun R x=>N () _ _⟩⟩
end YM.XSpace.Comets

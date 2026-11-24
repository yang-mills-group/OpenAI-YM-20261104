import YM.WilsonCoeffUV.Ward.Kinetic
/-!
# Exact chosen transverse cost at free. Positive-link bases. Scope native.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge}
-- compact d transfer
lemma cobound_test (i : TypeFace 2) (j:TypeFace 1)(f:Cover→ℝ): ∑' x,f x*cobound 1 i j x=∑ v:Axis, left ℝ 1 v i j*(f (step v)-f 0):=by
    classical
    rw [tsum_eq_sum (s:=Exterior.support)]
    · simp_rw [cobound, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _
      have he : (step v : Cover) ∈Exterior.support:= Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, Finset.mem_univ v, rfl⟩)
      have hc : (0:Cover)∈ Exterior.support:= Finset.mem_insert_self ..
      simp only [mul_sub, Finset.sum_sub_distrib,mul_ite,mul_zero,mul_one,Finset.sum_ite_eq',he,hc, ↓reduceIte]; ring
    intro b hb; rw [certified _ _ _ _ hb,mul_zero]
-- simplify hBlock point via finite legs.
lemma ccurv {α : Type*} (H:Row α (TypeFace 2))(i j) (x:Cover) : composeRows H (cobound 1) i j x = ∑ b: TypeFace 2,∑ v: Axis, left ℝ 1 v b j*(H i b (x-step v)- H i b x):=by
  unfold composeRows; apply Finset.sum_congr rfl; intro k _; unfold routed; rw [← (Equiv.subLeft x).tsum_eq (fun a=> _)]
  let f : Cover→ℝ:=fun a=> H i k (x-a)
  have ht:= cobound_test k j f; unfold f at ht; rw [sub_zero] at ht; rw [← ht]; apply tsum_congr; intro u; simp

lemma rslope {α:Type*}(R: Row (TypeFace 2) α)(i:TypeFace 1)(j)(x:Cover): composeRows (transRows (cobound 1)) R i j x= ∑ b:TypeFace 2, ∑ v:Axis,left ℝ 1 v b i*(R b j (x+step v)-R b j x):=by
    unfold composeRows; apply Finset.sum_congr rfl; intro k _; unfold routed transRows; rw [← (Equiv.neg Cover).tsum_eq (fun a=>_)]
    have hx:= cobound_test k i (fun a=> R k j (x+a)); rw [add_zero] at hx; rw [← hx]; apply tsum_congr; intro b; simp [mul_comm]

variable {η A:ℝ}
private lemma shift_graph {H:Cover→ℝ}(p:Width η A H)(hp:0<η)(f:Cover→ℝ)(b:Cover)(h:broad f):Summable fun x=> f x * H (x+b):=by
   let F x:= f (x+ -b) * H x
   have he:Summable F:= budget_poly p hp (h.around _)
   refine ((Equiv.addRight b).summable_iff.mpr he).congr (fun i=>?_); unfold F; simp
private lemma shift_poll (H f : Cover→ℝ)(b:Cover):∑' x,f x*H (x+b)=∑' x,f (x-b)*H x:=by
    rw [← (Equiv.subRight b).tsum_eq (fun x=>f x*H (x+b))]; simp
private lemma rise_marks {H:Cover→ℝ}(p:Width η A H)(hp:0<η)(f:Cover→ℝ)(b:Cover)(h:broad f): ∑' x,f x*(H (x+b)-H x)= ∑' x,(f (x+ -b)-f x)*H x:=by
    simp_rw [mul_sub, sub_mul]; let he:=budget_poly p hp h; rw [(shift_graph p hp f b h).tsum_sub he, Summable.tsum_sub ?_ he, shift_poll]; simp [sub_eq_add_neg]; exact budget_poly p hp (h.around _)
-- moments of R=H*d: constant & linear.
def squareB (x:Cover): ℝ:= (chalk 0 x)^2
lemma pulseM_mass (H:FaceRow){s A:ℝ}(_h:H.strip s A)(_hp:0<s)(he:H.read 0=1) (i j) : ∑' x,H i j x=if i=j then 1 else 0:=by
    apply Complex.ofReal_injective; rw [Complex.ofReal_tsum]; have ht:=congr_fun (congr_fun he i) j; by_cases h:i=j<;>simpa [h,Row.read,Laurent.read,mode_constant,Matrix.one_apply] using ht
lemma marks_copy {H:Row (TypeFace 2) (TypeFace 2)} (p:H.strip η A)(hp:0<η)(i:TypeFace 2)(j : TypeFace 1) {f:Cover→ℝ}(h:broad f) : ∑' x, f x * composeRows H (cobound 1) i j x= ∑ b,∑ v:Axis, left ℝ 1 v b j*∑' x,(f (x+step v)-f x)* H i b x:=by
  have hs b v: Summable (fun x=> f x * (left ℝ 1 v b j*(H i b (x-step v)- H i b x))) := by
    simp_rw [mul_left_comm (f _), mul_sub (f _),sub_eq_add_neg (a:= (_:Cover))]; exact (((shift_graph (p i b) hp f _ h).sub (budget_poly (p i b) hp h)).mul_left _)
  simp_rw [ccurv,Finset.mul_sum]; rw [Summable.tsum_finsetSum (fun i _=>summable_sum fun v _=>hs i v)]; apply Finset.sum_congr rfl; intro b _; rw [Summable.tsum_finsetSum (fun v _=> hs b v)]; apply Finset.sum_congr rfl; intro v _
  simp_rw [mul_left_comm (f _),tsum_mul_left]; congr 1
  convert! (rise_marks (p i b) hp f (-(step v:Cover)) h) using 1; simp [sub_eq_add_neg]
lemma flat_near {R:Row (TypeFace 2) (TypeFace 1)}(p:R.strip η A)(hp:0<η)(i:TypeFace 1) : ∑' x, squareB x*composeRows (transRows (cobound 1)) R i i x= ∑ b, left ℝ 1 0 b i*∑' x,((-2)*chalk 0 x+1)*R b i x:=by
    let h: broad squareB:= show broad (chalk 0^2) from (broad.chalk 0).power 2
    have hs b v:Summable (fun x=>squareB x*(left ℝ 1 v b i*(R b i (x+step v)-R b i x))):=by simp_rw [mul_left_comm (squareB _), mul_sub (squareB _)]; exact ((shift_graph (p b i) hp _ _ h).sub (budget_poly (p b i) hp h)).mul_left _
    simp_rw [rslope,Finset.mul_sum]; rw [Summable.tsum_finsetSum (fun i _=>summable_sum fun v _=> hs i v)]; apply Finset.sum_congr rfl; intro b _; rw [Summable.tsum_finsetSum (fun v _=> hs b v)]
    rw [Finset.sum_eq_single 0];
    · simp_rw [mul_left_comm (squareB _),tsum_mul_left]; rw [rise_marks (p b i) hp _ _ h]; congr 1; apply tsum_congr; intro x; congr 1; unfold squareB chalk; simp; ring
    · intro v _ hv; simp_rw [mul_left_comm (squareB _),tsum_mul_left]; rw [rise_marks (p b i) hp _ _ h]; have he x : squareB (x+ -(step v:Cover))= squareB x:= by simp [squareB,chalk,hv.symm]
      simp only [he,sub_self,zero_mul,tsum_zero,mul_zero]
    simp

private def comb: PlaqAxes:=⟨(0,1),zero_lt_one⟩
private def delta : TypeFace 2:= plaquette comb
lemma delta_value (i : TypeFace 2): left ℝ 1 0 i (coord 1)= if i=delta then 1 else 0 := by
    have hp : (0:Axis)∈delta.val:= by simp [delta,plaquette,comb]
    have hf : remove 0 delta hp=coord 1 := by ext; simp [remove,delta,plaquette,coord,comb]
    by_cases h:i=delta
    · subst i; rw [left,Matrix.of_apply,dif_pos hp,if_pos hf,if_pos rfl]; simp [Exterior.parity,pre]
    rw [left, Matrix.of_apply,if_neg h]; split; next ha =>
      rw [if_neg]; intro H; apply h; apply Subtype.ext; rw [← Finset.insert_erase ha, ← Finset.insert_erase hp]; congr 1; exact congr_arg Subtype.val (H.trans hf.symm)
    rfl
lemma one_font {H : FaceRow} (p:H.strip η A)(hp:0<η)(he:H.read 0=1) : ∑' x, squareB x * hBlock H (coord 1) (coord 1) x= -2:=by
    obtain ⟨C,hc,hK⟩ := cobound_ready 1 η
    rw [hBlock,flat_near (strip_compose hp.le p hK) hp]; simp_rw [delta_value]; simp only [ite_mul, Finset.sum_ite_eq', zero_mul,one_mul,Finset.mem_univ, if_true]
    let f (x:Cover):=((-2)*chalk 0 x+1)
    have ht: broad f:= (broad_gain (broad.chalk 0) (-2)).add broad.one
    rw [marks_copy p hp delta (coord 1) ht]
    have he' (x:Cover)(v:Axis): f (x+step v)-f x= if v=0 then -2 else 0:=by unfold f; rw [chalk_inc]; split <;> ring
    simp_rw [he',tsum_mul_left,pulseM_mass H p hp he]; simp [mul_ite,delta_value,ite_mul]

lemma orb_dawn {H : FaceRow} (p:H.strip η A)(hp:0<η)(he:H.read 0=1)(c:G.ColorIndex): azur (orbQ (plain G H)) c=1:= by
   let K:=orbQ (plain G H); unfold azur tailor
   rw [←(Equiv.neg Cover).tsum_eq (fun i=> _)]
   have h x : (chalk 0*chalk 0) ((Equiv.neg Cover) x)*petals K (coord 1,c) 1 c ((Equiv.neg Cover) x)= (squareB x*hBlock H (coord 1) (coord 1) x)*(2:ℝ)⁻¹:= by
     simp only [Pi.mul_apply]; change _ * (coloration G id id (hBlock H) ((coord 1,c):Hooks G) ((coord 1,c):Hooks G) (0- -x)/2)= _
     unfold coloration squareB chalk; simp; ring
   simp_rw [show ∀ x, (chalk 0*chalk 0) ((Equiv.neg Cover) x)*petals (orbQ _) _ _ c ((Equiv.neg Cover) x)=_ from h,tsum_mul_right,one_font p hp he]; norm_num
lemma crown_read (g:G.Simple)(A:Levels G) (N m:ℕ): readSun (orbQ (plain G (freeForms A N m)))=1:=by
   obtain ⟨s,a,hp,hh,H⟩:= forms_tail A.clock.kernel.penalty A.clock.kernel.penalty_pos _ (A.clock.adm m); have h:=(H A m rfl rfl).1 N; rw [read_azur _ (colI g)]; apply orb_dawn h hp
   unfold freeForms; rw [show ((record _).read 0)=pulse _ _ 0 from (heart_true _ A.clock.kernel.penalty_pos (A.clock.adm m) (location A N m)).1.echo _ (show 0∈baseCube from by simpa only [mon_zero] using mon_mem 1 (0:Site 1)), pulse_zero]
end YM.WilsonCoeffUV.Bank

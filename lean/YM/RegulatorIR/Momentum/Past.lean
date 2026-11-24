import YM.RegulatorIR.Momentum.Slope

/-! $d_1* H d_1$ moments without alias pole. This is why
comparison of TWO top choices at a hop uses p=2 null projection
identically. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry Spatial Sources Oracle Oracle.Quarry RG Bloch Precision Tree PertExtension Geometry.Field Exterior Work.F08
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X Y V:Type} {G:Gauge}{v p:ℕ}{σ τ A F:ℝ}
lemma d_mo (p:ℕ) (a:Room): wax (cobound p) 0 a=0:=by
 ext1 i j; apply Complex.ofReal_injective; change (wax (cobound p) 0 a|>.map ((↑):ℝ→ℂ)) i j=↑(0:ℝ);rw [wand0 (M:=cobound p),reading]; simp [symbol,wedge, Exterior.q, Matrix.sum_apply]
lemma tilt_b (n:ℕ)(p:Room)(M:Row X Y): wax (transRows M) n p=(wax M n (-p)).transpose:=by
 ext1 i j
 change (∑' x:Cover,M j i (-x)*_)=∑' x:Cover,M j i x * _
 rw [← (Equiv.neg Cover).tsum_eq (fun v=> M j i v * dial (-p) v^n)]
 apply tsum_congr;intro x; have ht: dial (-p) (-x)=dial p x:=by simp_rw [dial, Pi.neg_apply,Int.cast_neg,neg_mul_neg]
 change _= _*dial (-p) (-x)^_; rw [ht]; rfl

lemma wax_universal (n:ℕ)(a:Room){B:Bed} {p:Clip} {δ:ℝ} (H:Hall B σ F δ p) (hp:n≤2):
 wax (FreeResolvent.hBlock B.metric) n a=if n=2 then (2:ℝ) • ((wax (transRows (cobound 1)) 1 a)*(wax (cobound 1) 1 a)) else 0:=by
 have hB:= H.stripP.2.1; have hs:= H.pos; let d:= cobound 1; have h : d.strip σ _:= (FreeResolvent.cobound_ready 1 σ).choose_spec.2
 have hv:= strip_compose hs.le hB h
 unfold FreeResolvent.hBlock;rw [wax_mul (strip_trans h) hs hv];simp_rw [fun q:ℕ=>wax_mul hB hs h a q];
 have h':wax B.metric 0 a=1:=by
    ext1 i j; apply Complex.ofReal_injective; change (wax B.metric 0 a|>.map ((↑):ℝ→ℂ)) i j=_; rw [wand0 (M:=B.metric), (H.floorP 1).starts]; simp [Matrix.one_apply];split <;> simp
 have he:wax (transRows (cobound 1)) 0 a=0:= by rw [tilt_b,d_mo, Matrix.transpose_zero]
 interval_cases n <;> simp [d,Finset.sum_range_succ,he,h',d_mo,Matrix.one_mul,Matrix.mul_zero] -- test
lemma dipole (u:ℕ)(a:Room)(i j): wax (cobound u) 1 a i j= ∑ k : Axis, left ℝ u k i j * a k:=by
 rw [wax,Matrix.of_apply,recital,tsum_eq_sum (s:=Exterior.support)]
 · unfold cobound; simp_rw [Finset.sum_mul, pow_one]; rw [sum_comm]; apply sum_congr rfl;intro k _
   have hh:step k∈ Exterior.support:=mem_insert_of_mem (mem_image.mpr ⟨k,mem_univ _,rfl⟩)
   have he : (0:Cover)∈ Exterior.support:= mem_insert_self ..
   have hp:dial a (step k)=a k:=by simpa only [show Lattice.step k=(hop k:Cover) from funext (fun i=>by simp)] using dial_step a k
   simp only [mul_sub,mul_ite,mul_zero,mul_one,sub_mul,ite_mul,zero_mul, sum_sub_distrib, sum_ite_eq',if_pos hh,if_pos he,hp];simp [dial]
 intro x hx;rw [certified u i j x hx,zero_mul]
lemma edge_tip (b i:Axis) (j:TypeFace 2) : wax (cobound 1) 1 (step b) j (coord i)=left ℝ 1 b j (coord i):=by
 rw [dipole]; rw [Finset.sum_eq_single b]; simp;intro t _ ht;simp [ht];simp
lemma dial_opposite (p:Room)(z:Cover): dial (-p) z= -dial p z:=by simp only [dial,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
lemma opponent (M:Row X Y)(p:Room): wax M 1 (-p)= -wax M 1 p:=by
 ext1 i j; rw [wax,Matrix.of_apply,Matrix.neg_apply,wax,Matrix.of_apply,recital,recital]; simp_rw [pow_one,dial_opposite,mul_neg]; exact tsum_neg ..
lemma trans_pair {B:Bed}{p:Clip}{δ:ℝ}(H: Hall B σ F δ p) : wax (FreeResolvent.hBlock B.metric) 2 (step 0) (coord 1) (coord 1)=(-2:ℝ):=by
 rw [wax_universal 2 _ H (le_refl _), if_pos rfl, Matrix.smul_apply, Matrix.mul_apply, tilt_b 1, opponent]; simp_rw [Matrix.transpose_apply,Matrix.neg_apply,edge_tip]
 let a: TypeFace 2:= plaquette ⟨(0,1),by decide⟩
 have v:(0:Axis)∈ a.val:=by unfold a; simp [plaquette]
 have he : left ℝ 1 (0:Axis) a (coord 1)=1:=by
   unfold Exterior.left; rw [Matrix.of_apply, dif_pos v,if_pos]
   · unfold parity pre; rw [show (Finset.filter (fun i:Axis=>i<0) a.val).card=0 from by unfold a;decide]; simp
   apply Subtype.ext; change _ = ({1}:Finset Axis); unfold remove; unfold a; simp [plaquette]
 have ht(b:TypeFace 2)(hh:b≠a):left ℝ 1 0 b (coord 1)=0:=by
    unfold Exterior.left; rw [Matrix.of_apply]; split
    next v=>
      split
      next x=>
        exfalso;apply hh; apply Subtype.ext;rw [← Finset.insert_erase v, show b.val.erase (0:Axis)= _ from congr_arg Subtype.val x]; rfl
      rfl
    rfl
 rw [Finset.sum_eq_single a (fun b _ hb=>by rw [ht b hb,neg_zero, mul_zero]) (fun h=>False.elim (h (mem_univ _))),he]; norm_num [smul_eq_mul]
end YM.RegulatorIR.Momentum

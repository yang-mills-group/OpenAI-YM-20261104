import YM.XSpace.Compat.NativeDifference
import YM.XSpace.Sewn
import YM.XSpace.Wander

/-!
# Usable stencil position bounds for unconditioned potential lines
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sail
open YM.XSpace.Compat.KP
open Filter Set Function Lattice Bloch Laurent Complex MeasureTheory Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable (A:List Axis) (n:Side)
def dusk (x:Cover):=retract (city A) (rcast x)
lemma near_error : ∃ C:ℝ, 0≤C∧∀ n:Side,∀ x:Cover, ‖seen A n x-dusk A x‖≤ C*(1+‖rcast x‖)/n.val:=by
  obtain ⟨C,hC,H⟩:= ordinary_error A; refine ⟨‖(↑tally:ℂ)‖*C,by positivity,fun n x=>?_⟩
  rw [exposed,dusk,retract,← mul_sub,norm_mul]; apply (mul_le_mul_of_nonneg_left (H n (rcast x)) (norm_nonneg _)).trans_eq; ring
lemma toward {ι:Type*}{L:Filter ι} (n:ι→Side) (h:Tendsto (fun i=>(n i).val) L atTop) (x:Cover): Tendsto (fun i=> seen A (n i) x) L (𝓝 (dusk A x)):=by
  obtain ⟨C,hC,H⟩:= near_error A; exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _=>norm_nonneg _) (fun i=>H _ x) (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h)))

-- common notation for mesh lines & infinite stencil for pricing, all shifts forward for simplicity
private lemma next_next (i j : Axis) (p:Cover→ℂ): checkin i (checkin j p) = checkin j (checkin i p):=by funext x; simp only [checkin,add_right_comm x]; abel
def Δf {R E:Type*} [AddGroup R] [One R] [Sub E] (i : Axis) (p:Four R→ E):Four R → E :=fun x => p (x+step i)-p x
def crack {R E:Type*} [AddGroup R] [One R] [Sub E]: List Axis → (Four R→E)→ Four R→E
| [], p => p
| i::s,p=> Δf i (crack s p)
lemma crack_slot (p:Cover→ℂ): crack A p=slot checkin A p:=by
  induction A generalizing p with
  | nil=> rfl
  | cons i A ih => rw [slot,crack, ih p]; change checkin i (slot checkin A p)=_
                   clear ih; induction A generalizing p with
                   | nil =>rfl
                   | cons j A ih=> rw [slot,slot, ih (checkin j p), next_next]

def beam (A:List Axis) (n: Side) := crack A (Potential.G n)
lemma cracks (x:Cover): crack A (Potential.G n ∘ wrap n) x= beam A n (wrap n x):=by induction A generalizing x with
  | nil => rfl
  | cons i A ih => unfold beam at *; rw [crack,Δf,crack,Δf,ih,ih,map_add,wrap_step]
lemma read_beam (x:Cover): (beam A n (wrap n x):ℂ)= seen A n x:=by
  rw [← cracks,← seen_line,← crack_slot]; induction A generalizing x with
  | nil=> exact Potential.g_real ..
  | cons i A ih=> rw [crack,Δf, crack,Δf,Complex.ofReal_sub, ih,ih]

def cover (x: Cover):= (dusk [] x).re
lemma cracks_cover (x:Cover): (↑(crack A cover x):ℂ)=dusk A x:=by
  refine tendsto_nhds_unique (f:=fun p:ℕ => seen A (Top.side p) x) ?_ (toward _ Top.side Top.grows x); simp_rw [← read_beam]; apply (continuous_ofReal.tendsto _).comp (f:=fun i=> beam A (Top.side i) (wrap (Top.side i) x)) ?_
  induction A generalizing x with
  | nil =>
    have he := (continuous_re.tendsto _).comp (toward [] Top.side Top.grows x); apply he.congr (fun i=>?_); dsimp only [comp]; rw [← read_beam]; rfl
  | cons i A ih=>simp_rw [← cracks] at *; exact (ih (x+step i)).sub (ih x)

-- For lattice shells (cover max-norm)
def reach (x:Cover):ℕ:= Finset.univ.sup fun i:Axis=> (x i).natAbs
lemma reach_at (x:Cover)(i:Axis):(x i).natAbs≤reach x:= Finset.le_sup (s:=Finset.univ) (f:=fun i:Axis=>(x i).natAbs) (Finset.mem_univ i)
@[simp] lemma reach_zero : reach 0=0:=by simp [reach]
lemma reach_pos {x:Cover}(h:x≠0): 0<reach x:=by obtain ⟨i,hi⟩:= Function.ne_iff.mp h; apply lt_of_lt_of_le _ (reach_at x i); exact Int.natAbs_pos.mpr hi
lemma reached (x:Cover):∃ i:Axis, (x i).natAbs=reach x:=by obtain ⟨k,hk,H⟩:= Finset.exists_max_image Finset.univ (fun i:Axis=>(x i).natAbs) Finset.univ_nonempty; exact ⟨k,(reach_at x k).antisymm (Finset.sup_le H)⟩
lemma west (x:Cover): (reach x:ℝ)≤‖rcast x‖ ∧ ‖rcast x‖ ≤ 2*reach x:=by
  obtain ⟨i,hi⟩:= reached x; constructor
  · rw [← hi,Nat.cast_natAbs,Int.cast_abs, show ↑(x i)=(rcast x) i from rfl]; simpa only [basis_inner,basis_norm,one_mul] using abs_real_inner_le_norm (basis i) (rcast x)
  apply le_of_sq_le_sq _ (by positivity); rw [PiLp.norm_sq_eq_of_L2]; apply le_trans (Finset.sum_le_sum (g:=fun i=>(reach x:ℝ)^2) (fun i _=>?_)) _
  · exact le_of_eq (by simp [mul_pow]; norm_num)
  gcongr; rw [Real.norm_eq_abs,show (rcast x) i=(↑(x i):ℝ) from rfl, ← Int.cast_abs,← Nat.cast_natAbs]; exact_mod_cast reach_at x i
lemma reaches (x : Site n): reach (lift x)=pdist x:=rfl
lemma tree (x y:Cover): reach (x+y)≤reach x+reach y:=by obtain ⟨i,h⟩:=reached (x+y); rw [← h]; exact (Int.natAbs_add_le ..).trans (add_le_add (reach_at ..) (reach_at ..))
@[simp] lemma reach_neg (x:Cover):reach (-x)=reach x:=by simp [reach]

def carry (k:ℕ) (r:ℕ):ℝ := (1+(r:ℝ))⁻¹^k
lemma carry_pos (k r):0<carry k r:=by unfold carry; positivity
lemma grows_pay (k:ℕ)(x:Cover)(h:x≠0): (‖rcast x‖^k)⁻¹ ≤ 2^k *carry k (reach x):=by
  have hx:=reach_pos h; have he:1≤(reach x:ℝ):=by exact_mod_cast hx
  unfold carry; rw [← mul_pow,← inv_pow]; apply pow_le_pow_left₀ (by positivity)
  rw [← one_div ‖rcast x‖,← div_eq_mul_inv]; rw [div_le_div_iff₀ (by linarith [(west x).1]:0<‖rcast x‖) (by positivity)]; linarith [(west x).1]

lemma covers_decays : ∃ C:ℝ,0<C∧∀ x:Cover, |crack A cover x| ≤ C*carry (2+A.length) (reach x) := by
  obtain ⟨C,hC,H⟩ := at_bound A; let k:= 2+A.length; let q:=C*2^k; have hq : 0<q:=by unfold q; positivity
  refine ⟨q+ |crack A cover 0|,by positivity, fun x=>?_⟩
  by_cases h:x=0; simp [h,carry]; positivity
  have ht := cracks_cover A x; rw [← Real.norm_eq_abs,← Complex.norm_real,ht]
  have hh: 1≤(reach x:ℝ):=by exact_mod_cast reach_pos h
  apply (H _ (hh.trans (west x).1)).trans; apply (mul_le_mul_of_nonneg_left (grows_pay _ x h) hC.le).trans; unfold q; rw [add_mul, mul_assoc]; apply le_add_of_nonneg_right; positivity [carry_pos (2+A.length) (reach x)]
lemma cover_value : ∃ C:ℝ,0<C∧∀ x:Cover,1≤‖rcast x‖→ |crack A cover x-ride A Maxwell.Green (rcast x)|≤ C*(‖rcast x‖^(3+A.length))⁻¹:=by
  obtain ⟨C,hC,H⟩:= order_pay A; exact ⟨C,hC,fun x hx=> by rw [← Real.norm_eq_abs, ← Complex.norm_real,Complex.ofReal_sub,cracks_cover]; exact H _ hx⟩
lemma modulated : ∃ C:ℝ,0≤C∧∀ n:Side, ∀ x:Cover,‖spanRank n (rcast x)*seen A n x - dusk A x‖≤ C/n.val:=by
  obtain ⟨C,hC,H⟩ := modulation_carry A; refine ⟨‖(↑tally:ℂ)‖*C,by positivity,fun n x=>?_⟩; rw [exposed,dusk,retract,mul_left_comm, ← mul_sub,norm_mul]; exact (mul_le_mul_of_nonneg_left (H _ _) (norm_nonneg _)).trans_eq (mul_div_assoc _ _ _).symm
lemma seam : ∃ C : ℝ,0<C∧∀ n:Side,∀ x:Site n, |beam A n x|≤ C*(carry (2+A.length) (pdist x)+(n.val:ℝ)⁻¹):=by
  obtain ⟨D,hD,H⟩:= modulated A; obtain ⟨C,hC,K⟩ := covers_decays A; obtain ⟨b,hb,h⟩:= curtain_size; refine ⟨(C+D)/b,by positivity, fun n x=>?_⟩; let r:= rcast (lift x); have hw:=side_pos n; let k:=2+A.length
  have he (j:Axis): |leap n*r j| ≤ Real.pi:= local_price x j; specialize h n r he
  have hp : b*|beam A n x| ≤ D/n.val + C*carry k (pdist x):=calc
    _ ≤ ‖spanRank n r*seen A n (lift x)‖ := by rw [norm_mul,← read_beam,wrap_lift,norm_real,Real.norm_eq_abs]; gcongr
    _ ≤ ‖spanRank n r*seen A n (lift x)- dusk A (lift x)‖ + ‖dusk A (lift x)‖:=norm_le_norm_sub_add ..
    _ ≤ _ := add_le_add (H n (lift x)) (by rw [← cracks_cover,norm_real,Real.norm_eq_abs,← reaches n]; exact K _)
  rw [div_mul_eq_mul_div,le_div_iff₀ hb,mul_comm _ b]; apply hp.trans; rw [div_eq_mul_inv]; rw [show 2+A.length=k from rfl]; set e:=carry k (pdist x); have hq:0<e:=carry_pos ..; rw [← sub_nonneg]; ring_nf; positivity
lemma continuity_cost : ∃ C:ℝ,0≤C∧∀ n:Side,∀ x:Cover, |beam A n (wrap n x)-crack A cover x| ≤ C*(1+reach x)/n.val:=by
  obtain ⟨C,hC,H⟩:= near_error A; refine ⟨C*2,by positivity, fun n x=>?_⟩; rw [← Real.norm_eq_abs, ← norm_real,Complex.ofReal_sub,read_beam,cracks_cover]; apply (H n x).trans; have he:=side_pos n; rw [mul_assoc C]; gcongr; linarith [(west x).2]
end YM.XSpace.Sail

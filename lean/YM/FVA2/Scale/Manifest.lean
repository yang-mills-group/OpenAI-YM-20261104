import YM.FVA2.Scale.Functions
/-!
# Vanishing of nondiagonal budget

Homogeneous arrays in the sense `Equator.PurePower`. Use actual infinitesimal
NormStab, so prove the disappearance, not a hypothesis. Costs at each finite
horizon independently; resulting definitions then do commute with extension.
Strictly below the diagonal these contributions to a rotated field map
actually tend to zero (`fire`). Use with the log-polynomial requirement
(`bill`) to force them to be zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale.Manifest
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Facets Equator
local notation "L"=>FieldEnd
variable {G:Gauge}{n i j d l k:ℕ}
section recedes
variable (A:FieldEnd G d)(p:Sec G d)
private lemma low (h:Level.diag A=0)(j:E d) : proj j ( A ( proj j p ) )=0:= ( Level.diagonals .. ).symm.trans (h ▸ rfl) -- rewriting
lemma exp_times (h:i < j): Tendsto (fun t=> Extent.token t j * Extent.token (-t) i) atTop (𝓝 0):= by
    let n:ℕ:= j-i; have ht: 0<n:= Nat.sub_pos_of_lt h; have he:= Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot; obtain hv:= ( ( Complex.continuous_ofReal.continuousAt (x:=0) ).tendsto.comp he ).pow n; rw [Complex.ofReal_zero, zero_pow (by omega)] at hv; apply hv.congr; intro a; unfold Extent.token; unfold n; change (( ↑( Real.exp (-a)):ℂ ) ^ (j-i))=_ ; -- simplify cancellation
    let f:= ( Real.exp (-a):ℂ ); have hf:f ≠ 0:= Complex.ofReal_ne_zero.mpr (Real.exp_pos _|>.ne'); rw [ show j=(j-i)+i from (by omega), show j-i+i-i=j-i from (by omega),pow_add, neg_neg, show Real.exp a=(Real.exp (-a))⁻¹ from (by rw [Real.exp_neg,inv_inv]), Complex.ofReal_inv,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hf), mul_one ] -- argument name
lemma fire (F:Sec G d→ₗ[ℂ] ℂ)(h:Level.diag A=0)(H:Band A): Tendsto (fun t=> F (turner t A p)) atTop (𝓝 0):= by
    have hp (i:E d): Tendsto (fun t=> F (turner t A (proj i p))) atTop (𝓝 0):= by
       let B:= A (proj i p); let b (j:E d) t:ℂ:= (Extent.token t i.val * Extent.token ( -t ) j) * F (proj j B); have hb(t:ℝ): F (turner t A (proj i p))=∑ j:E d,b j t:= by
          change F (Level.Dial d ( -t ) (A (Level.Dial d t (proj i p))))=_; rw [ taken, _root_.map_smul ]; change F (Level.Dial d (-t) (Extent.token t i.val • B))=_; conv_lhs=> arg 2; rw [ _root_.map_smul,← Level.all B,map_sum, Finset.smul_sum ];
          rw [map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [Level.taken, smul_smul, _root_.map_smul ]; rfl
       have hx (j:E d): Tendsto ( b j ) atTop (𝓝 0):= by
          unfold b; rcases lt_trichotomy j i with hh|hh|hh; · exact (zero_mul (F (proj j B)) ) ▸ ( exp_times (show j.val < i.val from hh)|>.mul_const (F (proj j B)))
          · subst j; simp only [B, low A p h i, map_zero,mul_zero ]; exact tendsto_const_nhds
          simp only [B, stop p j H i hh,map_zero,mul_zero ]; exact tendsto_const_nhds
       simp_rw [hb]; exact ( Finset.sum_const_zero (M:=ℂ) (s:= Finset.univ (α:=E d)) ) ▸ tendsto_finsetSum ( Finset.univ ) (fun j _=> hx j)
    have he(t:ℝ): F (turner t A p)= ∑ i:E d,F (turner t A (proj i p)):= by rw [ ← map_sum, ← map_sum ]; congr 2; exact (Level.all p).symm
    -- no simp recursion via self p defeq
    conv => arg 1; ext; rw [he]
    exact ( Finset.sum_const_zero (M:=ℂ) (s:= Finset.univ (α:=E d)) ) ▸ tendsto_finsetSum _ (fun i _=> hp i)
end recedes
section tangent
variable (X: Way G d) (a b: Guard G d)
def response (x:Stage n)(p:Tags G d n): L G d →ₗ[ℂ] ℂ where
    toFun A:= ∑ i, iris x ( update p i ( A ( p i ) ) )
    map_add' u v:= by simp_rw [ LinearMap.add_apply, MultilinearMap.map_update_add,Finset.sum_add_distrib ]
    map_smul' c u:= by simp_rw [LinearMap.smul_apply,MultilinearMap.map_update_smul,Finset.smul_sum,RingHom.id_apply]
-- point version of `XSpace.Normalize.deviates` for reports
private lemma tally_le {a:Days n}(h:a∈ tally i n)(j): a j ≤ i:= ((totaled a).mp h) ▸ Finset.single_le_sum (f:=fun j=>a j) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
private lemma tuck {b:Days n}(h:b∈tally i n)(j:Fin n)(he:b (some j)=i): b= jumpDay n i j:= by
    ext1 k; let V:=some j; by_cases H:k=V; · subst k; rw [he]; exact Finsupp.single_eq_same.symm
    rw [jumpDay, Finsupp.single_eq_of_ne H]; have hz: ∑ k∈Finset.univ.erase V,b k=0:= by have hk:= Finset.add_sum_erase Finset.univ (fun i=> b i) (Finset.mem_univ V); rw [show b V=i from he, ( totaled b ).mp h ] at hk; omega
    exact ( Finset.sum_eq_zero_iff_of_nonneg (fun k _=>Nat.zero_le (b k)) ).mp hz k (Finset.mem_erase.mpr ⟨H,Finset.mem_univ _⟩)
theorem exhibits (hq:Equator.StarGround X) (h: i≠0) (hp: Base b) (H:∀ j < i,coeff j a=coeff j b)(x:Stage n)(p:Tags G d n) : actMark a X n x i p-actMark b X n x i p=response x p (coeff i a-coeff i b):= by
    unfold actMark; rw [seen, seen, ← Finset.sum_sub_distrib]; let f (c:Days n):= X n x (c none) (pulseU c a p) - X n x (c none) (pulseU c b p); let g:=jumpDay n i; let u:= Finset.univ.image g; change ∑ j∈tally i n,f j=_; have hv: u ⊆ tally i n:= by intro x hx; obtain ⟨i,_,rfl⟩:= Finset.mem_image.mp hx; exact jumping ..
    rw [← Finset.sum_subset hv (f:=f) ?_,Finset.sum_image (f:=f) (s:=Finset.univ) (g:=g) ((jumper h).injOn)]; swap
    · intro j hj ht; unfold f; apply sub_eq_zero.mpr; apply congr_arg; funext k; unfold pulseU; rw [ H _ ( lt_of_le_of_ne (tally_le hj _) (fun he=> ht (( tuck hj k he ).symm ▸ Finset.mem_image_of_mem g (Finset.mem_univ k))) ) ]
    refine Finset.sum_congr rfl (fun j _=>?_ ); unfold f g; simp_rw [ XSpace.Normalize.drift,H 0 (Nat.pos_of_ne_zero h),hp.zero,jumpDay,Finsupp.single_eq_of_ne (show none ≠ some j from (Option.some_ne_none _).symm) ]; simp only [ LinearMap.sub_apply,MultilinearMap.map_update_sub ]; rw [hq n x]; rfl
-- use Normstab.R.Angle
lemma sure (h:G.Simple) (H:FieldEnd G d)(ht:H∈ XSpace.Normalize.Change G d) (hp:∀ n (p:Stage n)(v:Tags G d n), response p v H=0): H=0:= by obtain hh:= normstab h (⟨H,ht⟩) ( ( XSpace.Normalize.genre _ ).mpr (fun n x hx v=> hp n ⟨x,hx⟩ v ) ); exact congr_arg Subtype.val hh
lemma unique (h:G.Simple)(ht: Base a)(hu:Base b)(H:StarGround X)(hp: actMark a X=actMark b X): a=b:= by
    refine PowerSeries.ext fun i=>?_ ; induction i using Nat.strong_induction_on with
    | _ i ih=> by_cases hc:i=0; · subst i; rw [ht.zero,hu.zero]
               apply sub_eq_zero.mp; apply sure h _ ( @Submodule.sub_mem ℝ (FieldEnd G d) _ _ _ (Normalize.Change G d) _ _ ( ht.high i hc ) (hu.high i hc) ); intro n p v; rw [ ← exhibits X a b H hc hu ih, hp,sub_self ]
-- depends on symmetry of scene through exact positive horizons. Uses MS removal for this
-- scale datum. (Free calc available; avoids using identities beyond posted geometry.)
variable {O:Booked (Press.portDeck G)}(T:MS_Data G O)(Y:Initialize G)(S:Prescription (Press.portDeck G))
variable (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)
include h hs
lemma fuel (H:StarGround X)(t:ℝ): StarGround ( scaling t X ):= fun n p=> MultilinearMap.ext (fun v=> ( Facets.scale_at .. ).trans (by rw [ H ]; exact iris_s T Y S h hs p v t ))
lemma bill (ht:Base a)(H:PurePower X)(hu:StarGround X)(he: PurePower (actMark a X)): Native a:= by
    let b:= Scale.diagonal a; apply Base.house.mpr; refine PowerSeries.ext fun i=>?_ ; induction i using Nat.strong_induction_on with
    | _ i ih=>
       change coeff i b = _; by_cases h0:i=0; · subst i; exact ht.payment.zero.trans ht.zero.symm
       let Z:= (coeff i a - coeff i b); have hz: Z∈Normalize.Change G d:=@Submodule.sub_mem ℝ (FieldEnd G d) _ _ _ (Normalize.Change G d) _ _ ( ht.high _ h0 ) ( ht.payment.high _ h0 ); have hp: Level.diag Z=0:= by unfold Z; have hx:Level.diag ( coeff i a - coeff i b )= _:= map_sub (Level.diag (G:=G) (d:=d)) (coeff i a) (coeff i b); rw [hx, Base.native a i, (show coeff i b=_ from (show coeff i b=Level.diag (coeff i a) from coeff_mk ..)),sub_self] 
       refine Eq.symm ( sub_eq_zero.mp ( sure h Z hz ?_ ) ); intro n p v; let f(t:ℝ):= response p v ( turner t Z );
       have hh(t:ℝ): scaling t (actMark a X) n p i v-scaling t (actMark b X) n p i v=f t:= by
          rw [ pose_act, pose_act ]; let s:=convertT t a; refine Eq.trans ( exhibits _ _ _ ( fuel X T Y S h hs hu t ) h0 (converts t b ht.payment) (fun j hj=> ?_) p v ) (congr_arg ( response p v ) ?_ ); -- order goals out?
          · simp only [convertT, coeff_mk]; exact congr_arg (turner t) (ih j hj).symm
          simp only [ Z, convertT, coeff_mk ]; exact (map_sub (Level.turner t) _ _).symm
       have hr:= ( he _ p v i ).sub ( FacetsP H n p v i ); -- helper
       change Rhythm (fun t=> scaling t (actMark a X) n p i v-scaling t (actMark b X) n p i v) at hr; simp_rw [hh] at hr; have hZ: Tendsto f atTop (𝓝 0):= by
           unfold f response; simp only [LinearMap.coe_mk,AddHom.coe_mk]; exact ( Finset.sum_const_zero (M:=ℂ) (s:= Finset.univ (α:=Fin n)) ) ▸ tendsto_finsetSum _ (fun j _=> fire Z (v j) ((iris p).toLinearMap v j) hp hz.2.1)
       replace hr:= congr_fun ( hr.asleep hZ ) (0:ℝ); simpa only [f,turner,LinearMap.coe_mk,AddHom.coe_mk, neg_zero, Level.flat, mul_one,one_mul, Pi.zero_apply ] using hr
where FacetsP (H:PurePower X) : PurePower (actMark (Scale.diagonal a) X):= powers_m _ _ H (Base.native _)
end tangent
end YM.FVA2.Scale.Manifest

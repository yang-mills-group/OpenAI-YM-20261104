import YM.PertExtension.GaussianIBP
import YM.Contacts.Pulse.Vision
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory
open Finset PertExtension.Series PertExtension.GaussianScore Pulse Pulse.Form MvPolynomial
open scoped Topology BigOperators ContDiff Classical
noncomputable section
variable {V : Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
variable {ι : Type} [Fintype ι]
local notation "E" => Plate ι
local notation "L" => Module.Dual ℝ V
variable {g:ι→ι→ℝ}
lemma ink_line (F:E)(i j:ι): pderiv i (pderiv j F)=pderiv j (pderiv i F):= by
  induction F using MvPolynomial.induction_on with
  | C=> simp
  | add A B ih il=> rw [map_add,map_add,map_add,map_add,ih,il]
  | mul_X A k ih=> simp_rw [pderiv_mul,map_add,pderiv_mul]; rw [ih]; have h (i j:ι) : pderiv i (pderiv j (X k:E))=0:= by by_cases he:k=j<;> simp [he]
                   rw [h,h]; ring
lemma lap_line (F:E)(i:ι): lap g (pderiv i F) = pderiv i (lap g F):= by
  simp only [lap_apply,map_sum,pderiv_C_mul]; exact sum_congr rfl fun j _=> sum_congr rfl fun k _=> congr_arg _ (by rw [ink_line (pderiv j F) i k, ink_line F i j])
def sand (g:ι→ι→ℝ)(i:ι)(F:E):= ∑ j,g i j • pderiv j F
lemma lap_sand (F:E)(i:ι): lap g (sand g i F)=sand g i (lap g F):= by unfold sand; simp_rw [map_sum,map_smul,lap_line]
lemma lap_X (h:g=flip g)(F:E)(i:ι): lap g (X i*F)=X i*lap g F+sand g i F := by
  simp_rw [lap_apply,mul_sum,sand,← C_mul',pderiv_mul,map_add,pderiv_mul,pderiv_X]
  let D j:= pderiv j F; let A:=fun j:ι => C (R:=ℝ) (σ:=ι) (g i j/2) * D j
  have he (k j : ι) : pderiv k (if i=j then (1:E) else 0)=0:=by split<;> simp
  -- split terms
  simp only [Pi.single_apply,he,zero_mul,zero_add, ite_mul,one_mul,zero_mul,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero, sum_const_zero,Finset.sum_ite_eq, Finset.mem_univ, if_true,mul_left_comm (X i : E)]
  rw [sum_comm]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]; rw [← add_assoc, add_comm, add_right_inj,← Finset.sum_add_distrib]; refine sum_congr rfl fun j _=> ?_; rw [show g j i=g i j from congr_fun (congr_fun h j) i,← add_mul,← map_add,show g i j/2+g i j/2=g i j by ring] 
lemma ladder (h:g=flip g)(F:E)(i:ι)(n:ℕ): stream g (X i*F) (n+1)= X i*stream g F (n+1)+sand g i (stream g F n):= by
  induction n with
  | zero=> simp only [stream,lap_X h,Nat.reduceAdd,Nat.cast_one,inv_one,one_smul]
  | succ n ih=>
    have H: lap g (stream g F n)=(n+1:ℕ) • stream g F (n+1):= by rw [stream,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
    rw [stream,ih,map_add,lap_X h,lap_sand,H]
    -- no overwriting nested
    let u:=sand g i (stream g F (n+1)); have hu : sand g i ((n+1:ℕ) • stream g F (n+1))=(n+1:ℕ) • u := by unfold u sand; rw [smul_sum]; simp only [map_nsmul]; exact Finset.sum_congr rfl fun i _=> smul_comm ..
    rw [hu]; rw (occs:=.pos [3]) [stream]
    change _ • (_ + u + (n+1) • u) = _ + u; rw [add_assoc _ u,show u+(n+1) • u=(n+1+1) • u by rw [add_smul (n+1),one_smul,add_comm], ← Nat.cast_smul_eq_nsmul ℝ, smul_add, mul_smul_comm, inv_smul_smul₀ (by positivity)]
lemma stream_rel (F:E)(i:ι)(n:ℕ): stream g (pderiv i F) n=pderiv i (stream g F n):= by induction n with | zero=>rfl | succ n ih=>rw [stream,ih,lap_line,stream,Derivation.map_smul]
lemma stream_add (F G:E)(n:ℕ): stream g (F+G) n=stream g F n+stream g G n:= by induction n with | zero=>rfl | succ n ih=>rw [stream,ih,map_add,smul_add,stream,stream]
lemma stream_scale (F:E)(s:ℝ)(n:ℕ): stream g (s • F) n=s • stream g F n:= by induction n with | zero=>rfl | succ n ih=>rw [stream,ih,map_smul,stream,smul_comm]
lemma stream_constants (c:ℝ)(n:ℕ): stream g (C c) (n+1)=0:= by induction n with | zero=> simp [stream,lap_apply] | succ n ih=> rw [stream,ih,map_zero,smul_zero]
section moment
variable (R:Law V)(T:ι→ Module.Dual ℝ V)(m:ι→ℝ)
local notation "ξ" => fun i j=> R.wick (T i) (T j)
def mark (F:E) := fun x:V=> MvPolynomial.aeval (m+ fun i=> T i x) F
lemma cost (F:E) : Zone.Invoice Radial.zone (mark T m F) ∧ Continuous (mark T m F):= by
  have H i : Zone.Invoice Radial.zone (mark T m (X i)) ∧ Continuous (mark T m (X i)):= by unfold mark; simp only [aeval_X,Pi.add_apply]; exact ⟨(Zone.Invoice.const _).add (Law.linearInvoice _),continuous_const.add (T i).continuous_of_finiteDimensional⟩
  induction F using MvPolynomial.induction_on with
  | C=> unfold mark; simp only [aeval_C,Algebra.algebraMap_eq_smul_one]; exact ⟨Zone.Invoice.const _,continuous_const⟩
  | add F G ih il=> rw [show mark T m (F+G)=_ from (funext (fun x=> map_add _ _ _) : _= mark T m F+mark T m G)]; exact ⟨ih.1.add il.1,ih.2.add il.2⟩
  | mul_X F i ih=> rw [show mark T m (F*X i)= _ from (funext (fun x=> map_mul _ _ _) : _= mark T m F*mark T m (X i))]; exact ⟨ih.1.mul (H i).1, ih.2.mul (H i).2⟩
variable [MeasurableSpace V][BorelSpace V] (μ:Measure V)[μ.HasTemperateGrowth]
lemma ink (F:E): Integrable (fun x=> mark T m F x * R.kern x) μ:= R.integrable_entry μ (cost T m F).1 (cost T m F).2
def paint : E →ₗ[ℝ] ℝ where
  toFun F:= R.average μ (mark T m F)
  map_add' F G := by unfold Law.average mark; simp only [map_add,Pi.mul_apply]; simp_rw [add_mul]; rw [integral_add (show Integrable (fun x=> aeval (m+fun i=> T i x) F*R.kern x) μ from ink R T m μ F) (show Integrable (fun x=> aeval (m+fun i=> T i x) G*R.kern x) μ from ink R T m μ G)]; ring
  map_smul' r F:= by simp only [Law.average,mark,Pi.mul_apply,map_smul]; simp_rw [smul_eq_mul, RingHom.id_apply,mul_assoc,integral_const_mul]; ring
lemma mat_hinge (F:E)(i:ι)(x y:V) (h:y=R.inverse (T i))(a:ℝ): HasDerivAt (fun t:ℝ=> mark T m F (x+t• y)) (mark T m (sand ξ i F) (x+a•y)) a := by
  induction F using MvPolynomial.induction_on with
  | C=> simp only [mark, aeval_C,sand,pderiv_C, smul_zero, sum_const_zero,map_zero]; exact hasDerivAt_const ..
  | add F G ih il=> rw [show sand ξ i (F+G)=sand ξ i F+sand ξ i G from by simp [sand,smul_add,Finset.sum_add_distrib]]; simpa only [mark,map_add] using! ih.add il
  | mul_X F j IH=>
    let V:= x+a•y; have H (r:ι): HasDerivAt (fun t:ℝ=>mark T m (X r) (x+t • y)) (R.wick (T i) (T r)) a := by simp_rw [mark,aeval_X,h,Pi.add_apply,map_add,map_smul]; simpa only [smul_eq_mul,one_mul,h, Law.wick] using! (((hasDerivAt_id' a).mul_const ((T r) y)).const_add (T r x)).const_add (m r)
    have hp:sand ξ i (F*X j) = sand ξ i F*X j + C (R.wick (T i) (T j)) * F:= by
       simp only [sand,pderiv_mul,smul_add,sum_add_distrib, sum_mul,add_right_inj, ← C_mul',mul_assoc, pderiv_X,Pi.single_apply,mul_ite,mul_zero,mul_one]; simp
    rw [hp]; convert! IH.mul (H j) using 1
    · ext t; simp only [mark,map_mul,Pi.mul_apply]
    simp only [mark,map_add,map_mul,aeval_X, aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; ring -- typo
lemma palette (F:E)(i:ι)[μ.IsAddRightInvariant] : paint R T m μ (X i*F)= m i*paint R T m μ F+ paint R T m μ (sand ξ i F):= by
   let p:= T i; let G:=sand ξ i F; have ht := R.translation_lemma (R.inverse p) (cost T m F).1 (cost T m F).2 (cost T m G).1 (cost T m G).2 (fun x=> fun t=> mat_hinge R T m F i x _ rfl t) μ
   rw [Law.applies] at ht; unfold paint Law.average
   let D x:= mark T m F x*R.kern x; let u:= ∫ x,R.kern x ∂μ; let H x:=mark T m G x*R.kern x; have hl: Integrable (fun x=> p x *D x) μ:= by
      let f : V→ℝ:= p; have hi:= R.integrable_entry μ (A:=f*mark T m F) ((Law.linearInvoice _).mul (cost T m F).1) ((LinearMap.continuous_of_finiteDimensional p).mul (cost T m F).2)
      simpa only [mul_assoc] using! hi
   change ((∫ x, mark T m (X i*F) x * R.kern x ∂μ)/u)= m i*((∫ x,D x ∂μ)/u) + (∫ x,H x ∂μ)/u
   have he : (∫ x,H x ∂μ) = ∫ x,p x*D x ∂μ:= sub_eq_zero.mp (by rw [← integral_sub (ink R T m μ G) hl]; convert ht using 2 ; funext x; simp only [H,D, Pi.sub_apply, Pi.mul_apply] <;> ring)
   rw [he]; have hp (x): mark T m (X i * F) x * R.kern x=m i*D x+p x*D x:= by unfold D mark p; simp only [map_mul,aeval_X,Pi.add_apply]; ring
   simp_rw [hp]; have he:=integral_add ((ink R T m μ F).const_mul (m i)) hl; erw [he,integral_const_mul]; ring -- check ∂
lemma deck_sync : (ξ)=flip ξ:= funext fun i=> funext fun j=> by change _=R.wick _ _; unfold Law.wick; rw (occs:=.pos [1]) [← R.applies (T j)]; rw (occs:=.pos [2]) [←R.applies (T i)]; rw [R.turns]
variable (g)
-- need `∀ p,repeated derivatives`. elimination finite.
def applause (F:E) (μ:Measure V)[μ.HasTemperateGrowth] := (∀ᶠ n:ℕ in atTop, stream ξ F n=0) ∧ ∀ᶠ n:ℕ in atTop, aeval m (∑ i∈Finset.range n,stream ξ F i)=paint R T m μ F
def drum (F:E) : List ι → E
| []=>F
| i::l=> drum (pderiv i F) l
def plot (F:E) := ∀ s, applause R T m (drum F s) μ
lemma applause_C (a:ℝ)[NeZero μ]: applause R T m (C a) μ:= by
  have hp: paint R T m μ (1:E)=1:= by change R.average μ (mark T m _) = 1; rw [show mark T m 1= 1 from funext (fun i=> by simp [mark]), R.empty]
  refine ⟨(eventually_ge_atTop 1).mono (fun n hn=> Nat.casesOn (motive:=fun n=>1≤n→stream ξ (C a) n=0) n (by exact fun h=> (by cases h)) (fun n h=>stream_constants ..) hn),?_⟩; filter_upwards [eventually_ge_atTop 1] with n hn; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [Finset.sum_range_succ']; simp_rw [stream_constants]; erw [Finset.sum_const_zero,zero_add]; change aeval m (C a)= _; rw [aeval_C, show (C a:E)=a • 1 from by simp [←C_mul'],map_smul,hp]; simp -- maybe simp
variable {F P:Plate ι}
lemma applause_add (h:applause R T m F μ)(hp:applause R T m P μ) : applause R T m (F+P) μ:= by
  simp only [applause,stream_add]; refine ⟨(h.1.and hp.1).mono (fun i hi=>by rw [hi.1,hi.2,add_zero]),?_⟩; filter_upwards [h.2,hp.2] with i hi hj; rw [Finset.sum_add_distrib,map_add,map_add,hi,hj]
lemma applauseX (h:applause R T m F μ)(hp:∀ j,applause R T m (pderiv j F) μ)[μ.IsAddRightInvariant](i:ι) : applause R T m (X i*F) μ:= by
  let f (X:E):= stream ξ X; let G:= X i*F; let s:=sand ξ i; have he:= fun k=> ladder (deck_sync R T) F i k
  simp_rw [sand,← stream_rel] at he
  have hs : Tendsto Nat.succ atTop atTop:= Filter.tendsto_atTop_mono (f:=id) (fun n=> Nat.le_succ n) tendsto_id
  simp only [applause] -- remove
  rw [← map_add_atTop_eq_nat 1]; constructor
  · refine eventually_map.mpr ?_; filter_upwards [hs.eventually h.1,eventually_all.mpr (fun j=>(hp j).1)] with n hn hu; change f _ (n+1)=0; unfold f; rw [he,hn]; simp [hu]
  refine eventually_map.mpr ?_; filter_upwards [hs.eventually h.2,eventually_all.mpr (fun j=>(hp j).2)] with n hn hu; have hy j := hu j
  rw [Finset.sum_range_succ']; simp_rw [he,sum_add_distrib]; rw [sum_comm (f:=fun k:ℕ=> fun j:ι=> _),← mul_sum]; rw [stream,add_right_comm, ← mul_add, show (∑ i∈ Finset.range n,stream ξ F (i+1))+F= _ from (Eq.symm (Finset.sum_range_succ' (stream ξ F) n)),map_add,map_mul,aeval_X,hn,palette]
  simp_rw [← smul_sum, map_sum, map_smul,hy,sand,map_sum,map_smul]
lemma drum_add (x y:E)(s:List ι): drum (x+y) s=drum x s+drum y s:= by induction s generalizing x y with | nil=>rfl | cons i s ih=> rw [drum, map_add,ih,drum,drum]
lemma plot_add (h:plot R T m μ F)(hp:plot R T m μ P) : plot R T m μ (F+P):=by intro i; rw [drum_add]; exact applause_add _ _ _ _ (h i) (hp i)
lemma plot_X_mul (h:plot R T m μ F) [μ.IsAddRightInvariant] (i:ι): plot R T m μ (X i*F):= by
  intro s; induction s generalizing F with
  | nil=> exact applauseX _ _ _ _ (h []) (fun j=> h [j]) _
  | cons j s ih=>
    have he := ih (F:=pderiv j F) (fun l=> h (j::l)); rw [drum,pderiv_mul]; by_cases hy:j=i
    · rw [hy,pderiv_X_self,one_mul,drum_add]; exact applause_add _ _ _ _ (h _) (hy ▸ he)
    rw [pderiv_X_of_ne (Ne.symm hy),zero_mul,zero_add]; exact he
lemma plot_const (a:ℝ)[NeZero μ]: plot R T m μ (C a):= by intro s; induction s generalizing a with | nil=> exact applause_C _ _ _ _ a | cons i s ih=> rw [drum,pderiv_C, ← MvPolynomial.C_0]; exact ih _
theorem read_frame (F:E)[NeZero μ][μ.IsAddRightInvariant] : applause R T m F μ:= by
  suffices h: plot R T m μ F from h []; induction F using MvPolynomial.induction_on with
  | C=> exact plot_const R T m μ _
  | add _ _ ih il=>exact plot_add R T m μ ih il
  | mul_X f i h=> rw [mul_comm]; exact plot_X_mul _ _ _ _ h i

theorem finish [NeZero μ][μ.IsAddRightInvariant]{F:ℕ→Rack ι}(h:Snug F) (e:ℕ) : paint R T m μ (PowerSeries.coeff e (breath (clouds F)))= aeval m (PowerSeries.coeff e (breath (clouds (massaged ξ F)))):= by
  obtain ⟨n,hh⟩:= eventually_atTop.mp (read_frame R T m μ (PowerSeries.coeff e (breath (clouds F)))).2
  rw [wick_heat_finite _ F h (max n (3*e)) e (le_max_right ..)] -- h shadow
  exact (hh (max n (3*e)+1) (by omega)).symm
end moment
end
end YM.Contacts.Milling

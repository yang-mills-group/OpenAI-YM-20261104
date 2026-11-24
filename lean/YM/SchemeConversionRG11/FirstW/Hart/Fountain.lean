import YM.SchemeConversionRG11.FirstW.Hart.Rays
/-! Use at external smooth arrays from separate points. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Metric Lattice Pert Align Maxwell Topology
open scoped BigOperators Classical
open Laurent (size)
variable {T : Itinerary} {G : Gauge} {n : Side}
def access (T : Itinerary) (R : ℝ) := ∀ᶠ i in atTop,∀ x:Cover,T.gap i * (size x:ℝ)≤R → lift (wrap (T.period i) x)=x
lemma entrance (T : Itinerary) (R : ℝ) : access T R := by
  filter_upwards [(large T).eventually (eventually_gt_atTop (2*R))] with i hi
  intro x hx; refine lift_eq_iff.mpr ⟨rfl,fun j=>?_⟩; apply (?_ : -(T.period i).val < 2*x j ∧ _); have he : (2:ℕ)* (size x) < (T.period i).val := by
    have hy : (2:ℝ)*(size x:ℝ)<(T.period i).val := by nlinarith [T.positive i];
    exact_mod_cast hy
  have := (yard_upper x j).trans (yard_size x); omega
lemma smallE (x : Cover) (i : ℕ) : ‖Full.incVec (T.gap i) x‖ ≤ 2 * (T.gap i*(size x:ℝ)) := by
  rw [mover_norm _ (T.positive i).le]; apply le_trans (mul_le_mul_of_nonneg_left (yard_fromE x) (T.positive i).le); rw [mul_left_comm]; gcongr; · exact (T.positive i).le
  exact yard_size _
lemma bound_order (A : Sight T G) (Y : ℕ→Field4 G) {R : ℝ} (hr: R>0) {P : Axis → Sheets G.Color} (e : ∀ a, Score T (Metric.closedBall 0 (2*R)) (fun i x=>(T.gap i)⁻¹ • A i (x,a)) (P a)) (hp : ∀ i,Y i=terms 0 (A i)) (k : ℕ) : Warrant T R k Y ∧ Mon T k Y := by
  have he (a:Axis) (x : Cover) i : field4 a (Y i) x = A i (wrap (T.period i) x,a) := by rw [hp]; simp [field4,terms]
  have hh (i:ℕ) (a : Axis) (p:Cover) (l : List Axis) :
      surface l (T:=T) (fun i x=>(T.gap i)⁻¹ • A i (x,a)) i (wrap (T.period i) p) = (T.gap i^(l.length+1))⁻¹ • combine l (field4 a (Y i)) p := by
    rw [show field4 a (Y i)=(field4 a (A i)) ∘ wrap (T.period i) from funext fun x=> he a x i,combine_wrap, surface]
    rw [show (fun x=> (T.gap i)⁻¹ • A i (x,a))= (T.gap i)⁻¹ • field4 a (A i) from rfl,combine_smul]; simp only [comp_def,Pi.smul_apply, smul_smul,pow_add,pow_one,mul_inv]
  have H (a : Axis) (l : List Axis) := Meets.rent (K:=Metric.closedBall (0:E4) (2*R)) (e a l) (isCompact_closedBall ..) (Subset.refl _)
  choose C hc hC using H
  constructor
  · let b (v : Axis×Trad (k+1)) := C v.1 (List.ofFn v.2.2)
    refine ⟨1+∑ v,b v, add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun x _=>(hc ..).le),?_⟩
    have hs : ∀ᶠ i in atTop,∀ a : Axis,∀ l:List Axis,l.length=k+1 → ∀ x:Site (T.period i), ‖out T i x‖ ≤2*R → ‖surface l (T:=T) (fun i x=>(T.gap i)⁻¹ • A i (x,a)) i x‖ ≤ C a l :=
      (eventually_all.mpr fun a:Axis=> eventually_all.mpr fun l:Trad (k+1)=> hC a (List.ofFn l.snd)).mono (fun i hi a l e x hx=> by obtain ⟨t,ht⟩:=lists l (d:=k+1) e.le; rw [←ht]; exact hi a t _ (by simpa using hx))
    refine ((show access T R from entrance T R).and hs).mono (fun i hi a l h0 x hx=>?_)
    have he : ‖out T i (wrap (T.period i) x)‖ ≤ 2*R := by unfold out; rw [hi.1 x hx]; exact (smallE (T:=T) x i).trans (by linarith)
    have hr := hi.2 a l h0 _ he; have ht := pow_pos (T.positive i) (l.length+1); rw [hh,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le,inv_mul_le_iff₀ ht,h0] at hr; apply le_trans hr; rw [mul_comm (T.gap i^(k+1+1))]; refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (T.positive i).le _)
    obtain ⟨t,ht⟩:=lists l h0.le; rw [←ht]; exact (Finset.single_le_sum (f:=b) (fun x _=> (hc ..).le) (Finset.mem_univ (a,t))).trans (le_add_of_nonneg_left zero_le_one)
  intro j hj D a v; let l:=List.ofFn D
  have hv := e a l _ tendsto_id 0 (mem_closedBall_self (by linarith)) _ (sails_step (T:=Rig.path T id tendsto_id) 0)
  refine ⟨_,((innerSL ℝ (unitColor G v)).continuous.continuousAt.tendsto.comp hv).congr ?_⟩
  intro i; change inner ℝ (unitColor G v) (surface l (T:=T) _ i ((wrap (T.period i)) 0))=_; rw [hh,show l.length=j from List.length_ofFn,real_inner_smul_right];rfl
-- stationarity at fixed offsets only.
lemma fixed_needle (x : StepPath T) {v : E4} (he : sails T x v) (hx : v≠0) (w : Cover) : ∀ᶠ i in atTop,x i ≠ wrap (T.period i) w := by
  have hg := sails_step (T:=T) w; have hp := Tendsto.prodMk_nhds he hg
  have H0:= isOpen_ne_fun continuous_fst continuous_snd|>.mem_nhds (show (v,0) ∈ {p:E4×E4|p.1≠p.2} from hx)
  have ht : ∀ᶠ i in atTop, out T i (x i) ≠ out T i (wrap (T.period i) w) := by filter_upwards [hp.eventually H0] with i hi; exact hi
  exact ht.mono fun i hi h=> hi (congrArg _ h)
lemma ladder_walk (k : Labels.Key G) (x : StepPath T) {v : E4} (he : sails T x v) (hv : v≠0) (l : Cover) (j : Axis) : ∀ᶠ i in atTop, ladder (native k (x i)) (wrap (T.period i) l,j)=0 := by
  have ha (a : Atom k.1) : ∀ᶠ i in atTop,∀ b:G.Color,∀ t:G.Color, eman (x i) a b (needle (wrap (T.period i) l,j) t)=0 := by
    apply (eventually_all.mpr (fun q:Atom.Kind k.1=> fixed_needle x he hv (l-a.offset q))).mono; intro i hi b t
    unfold eman; rw [LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro t₀ _; rw [LinearMap.smul_apply, pinch_eq, pinched, if_neg, inner_zero_right,smul_zero]; intro ht; refine hi t₀ ?_; rw [map_sub, eq_sub_iff_add_eq]; exact congrArg Prod.fst ht
  filter_upwards [eventually_all.mpr (fun s:Signed=> eventually_all.mpr fun u:Spot G k.1 => ((ha (u.atom s)).and (ha (Align.swap (u.atom s)))))] with i hi
  apply ink_zero; intro t; rw [ladder_val,letter_exact,LinearMap.sum_apply, Finset.sum_eq_zero]; intro s _; rw [LinearMap.sum_apply,Finset.sum_eq_zero];intro u _; simp only [LinearMap.smul_apply,LinearMap.sub_apply,(hi s u).1,(hi s u).2,sub_zero,smul_zero]
lemma detectors_echo (k : Labels.Key G) (x : StepPath T) {v : E4} (he : sails T x v) (hv : v≠0): Echoes (fun i=> terms 0 (river (T.gap i) k (x i))) := by
  constructor
  · intro y a; filter_upwards [ladder_walk k x he hv y a] with i hi
    let V:= river (T.gap i) k (x i)
    change atoneLap (field4 a (terms 0 V)) y=0; rw [show atoneLap _ _= Orb.lap (Orb.row V a) (wrap (T.period i) y) from by simp [Orb.lap,terms,field4,atoneLap,Orb.row]]
    have H:= water (native k (x i)) (fun p=>letter_C _ _ _ p) a (wrap (T.period i) y)
    have hV : ∀ A : FullT G (T.period i),∀ t : ℝ, Orb.lap (Orb.row (t • A) a) (wrap (T.period i) y)=t • Orb.lap (Orb.row A a) (wrap (T.period i) y) := by intro A t; simp [Orb.lap,Orb.row,two_nsmul]; simp only [← smul_comm t (4:ℕ),smul_sub,smul_add,Finset.smul_sum]
    unfold V river canal; rw [hV,H,hi,neg_zero,smul_zero]
  intro y; apply Eventually.of_forall; intro i; have he:= congrFun (east_free (p:=tape k (T.gap i) (x i)) (fun σ=>by rw [show Orb.grad σ=momentE σ from rfl]; exact letter_T k (T.gap i) (x i) σ)) (wrap (T.period i) y)
  rw [show atoneDiv (terms _ _) y= Orb.divB (river (T.gap i) k (x i)) (wrap (T.period i) y) from ?_,gauged]; exact he
  simp [Orb.divB,terms,atoneDiv]
end YM.RG11.FirstW

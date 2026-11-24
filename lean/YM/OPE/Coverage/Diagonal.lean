import YM.OPE.Coverage.Census

/-!
## Engineering charges for physical inverse labels using any sufficiently
wide dense shelf at the *same* weak tests.

Reflection positivity is used for the Maxwell target via the covariance
Gram test, not assumed at a cutoff selected after moving a physical label.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace YM.OPE.Coverage
open Set Function MeasureTheory Filter Ward Extraction Climb Table Spec Next.UVStress
open scoped Topology BigOperators ContDiff Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(H: Final C F S){r:ℕ→ℝ}{D n d e:ℕ}{R:ℝ}
variable (p:Shelf H r D n R) (x:S.Field e) -- x at grade e, risen to d
variable (h₀:Services C F S) (he: e ≤ d)
local notation "U" => p.maps
local notation "X" => S.Field
local notation "V" => (Bel C.book).Field
local notation "clock" => mark (p.path)
local notation "ℬ" => Levy.bar H
local notation "τ" => H.sector.derivatives.rise
open Orbits
private def letters{m:ℕ}(x: ℕ→ℝ)(g:ℕ→Fin m →E4)(i:ℕ) : (Fin m ⊕ PEmpty.{1})→E4 := beside (fun j=> x i • g i j) PEmpty.elim
private def glyph {m}(w:Fin m→C.book.Token): (Fin m ⊕ PEmpty.{1})→C.book.Token := beside w PEmpty.elim

include p h₀ in
lemma clear_rate {m:ℕ} (w:Fin m→ C.book.Token) (z: ℕ→Points m) (c:ℝ)(hc:0 < c)
    (hz:∀ᶠ i in atTop,∀ j l:Fin m,j ≠ l → c ≤ cubedist (z i j) (z i l)):
    RateLE atTop clock (fun i=> observe S ((p.path i • z i).ofLp) w) (sigma w:ℝ) := by
  let g i:= (z i).ofLp
  let y i:=fun j: Fin m=>p.path i • g i j
  have hZ: Kept atTop clock 1 y:=by
    intro b hb
    have hu:=((RateIs.exp (l:=atTop) (-b) p.fades.2).div (RateIs.exp (-1) p.fades.2))
    have h := (hu.tends (by linarith only [hb]) p.fades.2).eventually (gt_mem_nhds hc)
    filter_upwards [h,hz] with i hi he j j' hj
    have ht: c ≤ ‖g i j-g i j'‖ :=?_ -- cubedist upper ≤ norm
    have he' : Real.exp (-1*clock i) = p.path i := by rw [mark,neg_one_mul,neg_neg,Real.exp_log (p.fades.1 i)]
    replace hi : Real.exp (-b*mark p.path i)/Real.exp (-1*mark p.path i) < c:= hi
    rw [show y i j - y i j'= p.path i • (g i j - g i j') from (smul_sub ..).symm]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (p.fades.1 _)]
    exact (div_lt_iff₀ (Real.exp_pos _)).mp (show _ < _ from hi) |>.trans_le (mul_comm (p.path i) _ ▸ he' ▸ (mul_le_mul_of_nonneg_right ht (Real.exp_pos _ |>.le)))
    -- orientation may not elaborate
    have : cubedist (z i j) (z i j') ≤ ‖z i j-z i j'‖:=by
       unfold cubedist
       rw [dist_eq_norm]
       -- compare Pi sup over axes
       rw [pi_norm_le_iff_of_nonneg (norm_nonneg (z i j-z i j'))]
       intro a
       exact PiLp.norm_apply_le (z i j-z i j') a
    exact le_trans (he _ _ hj) this 
  have hK: Kept atTop clock 1 (fun _:ℕ=> (PEmpty.elim : PEmpty.{1}→E4)):= fun _ _=> (Filter.Eventually.of_forall (fun i j=>j.elim))
  have hH: Intervals atTop clock 1 y (fun i=> (PEmpty.elim : PEmpty.{1}→E4)):= by
    intro b hb
    exact Filter.Eventually.of_forall fun i j j'=>j'.elim
  let b:PEmpty.{1}→C.book.Token:=PEmpty.elim
  have U₀:= viewer_cost H h₀.schedule w b p.fades.2 (fun i=>none) hZ hK hH zero_le_one le_rfl
  have hf : sigma w * (1:ℝ) + sigma b * 1 = (sigma w:ℝ) :=by rw [show sigma b=0 from Finset.sum_of_isEmpty ..]; simp
  rw [hf] at U₀
  apply U₀.congr
  filter_upwards [hZ.inject] with i hi
  let e:=Equiv.sumEmpty (Fin m) PEmpty.{1} -- orientation?
  have hx := perm_observe S H.room.kernel.laws.toSymmetric e w hi
  have hh: beside w b = w ∘ e:=by
    ext1 x; rcases x with l|l; · rfl
    exact l.elim
  have hy: beside (y i) PEmpty.elim = y i ∘ e:=by
    ext1 j; rcases j with l|l; · rfl
    exact l.elim
  change observe S (beside (y i) PEmpty.elim) (beside w b) = _
  rw [hh,hy,hx]
  rfl
private lemma fin_eta {m n} {C:Register G}(S:Table C)(z:Points n)(v:Fin n→ S.Tag)(h:m=n): disc v z = S.useAt S (points fun i:Fin m=> z.ofLp (Fin.cast h i)) (v ∘ Fin.cast h):= by subst m;rfl
private lemma fin_moment {m} {C:Register G}(S:Table C)(z:Points m)(v:Fin m→ S.Tag)(h:S.Hierarchy)(hz:z∈conf m):
   disc v z=moment S (S:=S) (d:=fun i=>(v i).1) (z.ofLp) fun i=>(v i).2 :=by
   -- permute enumeration from runNames to Fin.cast
   let f:=finCongr (Fintype.card_fin m)
   let g:= (runNames (Fin m)).symm.trans f
   have he:= permuted (T:=S) (a:=fun i=>(v i).2) (y:=z.ofLp) h hz g
   rw [←he]
   refine Eq.trans (fin_eta S z v (h:=Fintype.card_fin m)) (congr_arg₂ (S.useAt S) (congr_arg points (funext fun i=>?_)) (funext fun i=>?_))
   · change z (f i)= z (g (runNames _ i)); rw [show (g (runNames _ i)) = f i from ?_]
     simp [g,f]
   change v (f i) = Sigma.mk _ ((v (g (runNames (Fin m) i))).2)
   rw [show (g (runNames _ i)) = f i from by simp [g,f]]

include he
lemma reflects {x y:S.Field e}(t:Test 2)(q:ℝ)(hl:0<q) : scene S d q t (τ he x) (τ he y)=scene S e q t x y:=by
  let v :Fin 2→ S.Tag:= blit S e x y
  let w :Fin 2→S.Tag := blit S d (τ he x) (τ he y)
  have hr (i:Fin 2) : (v i).1 ≤ (w i).1:=by fin_cases i <;> exact he
  have hp (i:Fin 2): (τ (hr i) ((v i).2))=(w i).2:=by fin_cases i<;>rfl
  have hg(u:Fin 2→S.Tag)(i:Fin 2): update u i ⟨(u i).1,(u i).2⟩=u:=by
    ext1 j; by_cases he:j=i; · subst j; exact update_self ..
    exact update_of_ne he ..
  let g:= update v 0 (w 0)
  unfold scene
  refine t.apply_eq (fun z hz=>?_)
  have hz:= (enlarged (n:=2) hl z).1 hz
  have ht(u i): disc (update u i (w i)) (q • z) = disc (update u i (v i)) (q • z):= by
     change S.useAt S _ _ = S.useAt S _ _
     rw [← show Sigma.mk _ (τ (hr i) ((v i).2))=w i from Sigma.ext rfl (heq_of_eq (hp i))]
     apply DiffPlan.inclusion_slot
     · exact H.phase.transport.injection
     · exact H.room.kernel.laws.toSymmetric
     exact hz
  change disc w _ = disc v _
  have h1 : g 1=v 1:=update_of_ne (by decide) ..
  calc _ = disc (update g 1 (w 1)) (q • z) := by congr; ext1 i; fin_cases i <;> simp [g]
       _ = disc g _ := ((ht g 1).trans (congrArg (fun v=> disc (update g (1:Fin 2) v) (q • z)) h1.symm)).trans (congrArg (fun u=>disc u (q • z)) (hg g 1))
       _ = disc v _ := (ht v 0).trans (congrArg (fun u=> disc u (q • z)) (hg v 0))
open Next.UVStress Analysis
variable (hn:2≤n)(hD:d≤D)(ha:0<R)(hh:∀ t∈silver C d, tsupport t ≤ Scaling.window R 2)
include hn hD ha hh
section
omit hn hD he
include p h₀

-- Actual-field readings on fixed silhouettes of the measured path
lemma fixed_moments (y:S.Field e)(t:Test 2)(ht:t∈silver C d):
    RateLE atTop (mark p.path) (fun i=> scene S e (p.path i) t x y) (e+e:ℝ):=by
  let c:ℝ:=R⁻¹
  -- strict half-clearance also at ties
  let c':ℝ:= c/2
  let E:= airy 2 c'
  let v:=blit S e x y
  let u:Fin 2→C.book.Token:=names (d:=fun i=>(v i).1) (S:=S) (fun i=>(v i).2)
  have hu: (sigma u:ℝ) = (e+e:ℝ):=by simp [sigma,u,v,names,blit,Fin.sum_univ_succ]
  have hg(z:ℕ→E): RateLE atTop clock (fun i=> pointwise S e (p.path i) x y (z i)) ((sigma u:ℝ)):= by
     let z₀:=fun i=> (z i).val
     have hz (i:ℕ): z₀ i∈conf 2:=spaced_conf (half_pos (by positivity : 0<c)) (fun j l he=>(z i).prop j l he|>.le)
     apply (clear_rate H p h₀ u z₀ c' (half_pos (by positivity)) (Eventually.of_forall fun i j l he=>(z i).prop j l he|>.le)).congr
     filter_upwards with i
     have h' : pointwise S e (p.path i) x y (z i)=disc v (p.path i • z₀ i):=rfl
     rw [h',fin_moment S _ _ H.room.kernel ((enlarged (p.fades.1 _) (z₀ i)).1 (hz i)),OPE.Orbits.observed]
  -- integrate uniformly by selection
  have hf (i:ℕ) : Integrable (fun z:Points 2=> t z * pointwise S e (p.path i) x y z):= by exact t.smearing ((smoothZoom H.room.kernel.smooth _ (p.fades.1 i)).continuousOn)
  let mass:= (∫ z:Points 2, ‖t z‖)
  intro b hb
  obtain ⟨α,hα,hα'⟩ := exists_between hb
  have hprice: ∀ᶠ i in atTop, ∀ z∈ tsupport t, ‖pointwise S e (p.path i) x y z‖ ≤ Real.exp (α*clock i):=by
     by_contra! he'
     have h(i:ℕ):= (frequently_atTop.mp he') i
     choose f hL v hv h' using h
     have fvg:= tendsto_atTop_mono (f:=id) hL tendsto_id
     have hv0(i): v i∈E := fun j l e'=> lt_of_lt_of_le (half_lt_self (by positivity : 0 < c)) ((hh t ht (hv i)).1 j l e')
     let g(i:ℕ):E:=⟨v i,hv0 i⟩
     let p' i:E:= if h:∃ j,f j=i then g (Nat.find h) else g 0
     exfalso
     have h_p:= fvg.eventually ((hg p') α (hu.symm ▸ hα))
     let i:=h_p.exists.choose
     let j:=Nat.find (show ∃ j,f j=f i from ⟨i,rfl⟩)
     have hj:f j=f i:= Nat.find_spec (p:=fun l=>f l=f i) ..
     have h:= h_p.exists.choose_spec
     have hz:p' (f i)=g j:= dif_pos _
     change ‖pointwise S _ (p.path (f i)) x y _‖ ≤ _ at h
     rw [hz] at h
     exact not_le.mpr (hj ▸ (show _ < _ from h' j)) (show _ from h)
  filter_upwards [hprice,(RateLE.const mass p.fades.2) (b-α) (sub_pos.mpr hα')] with i hi hV
  let f:= pointwise S e (p.path i) x y
  calc ‖_‖ = ‖∫ z:Points 2,t z*f z‖ :=rfl
       _ ≤ ∫ z:Points 2, ‖t z*f z‖ :=norm_integral_le_integral_norm _
       _ ≤ ∫ z:Points 2, ‖t z‖*Real.exp (α*clock i) := by
          apply integral_mono (hf i|>.norm) ((t.continuous.integrable_of_hasCompactSupport t.hasCompactSupport).norm.mul_const _) (fun z=>?_)
          rw [norm_mul]
          by_cases e:z∈tsupport t
          exacts [mul_le_mul_of_nonneg_left (hi _ e) (norm_nonneg _), by rw [image_eq_zero_of_notMem_tsupport e]; simp]
       _ = mass*Real.exp (α*clock i):=by rw [integral_mul_const]
       _ ≤ _:=by
          refine (mul_le_mul_of_nonneg_right (by linarith only [hV,le_abs_self mass,(Real.norm_eq_abs mass)] : mass ≤ Real.exp ((b-α)*clock i)) (Real.exp_pos _).le).trans ?_
          rw [← Real.exp_add, sub_mul]; simp
end
omit hn ha hh hD in
lemma bar_shift: ℬ d (τ he x) = τ he (ℬ e x):=by
   unfold Levy.bar; rw [H.phase.transport.rights.realInc,H.phase.transport.rights.mirrorInc]

include h₀
lemma shelf_inverse_preimage (a:ℝ)(ha':(e:ℝ)<a):
     ∀ᶠ i in atTop, ∀ v: V d, U i d v= τ he x → ‖v‖ ≤ Real.exp (a*clock i):= by
   let P(t:Test 2)(i:ℕ) := scene S e (p.path i) t x (ℬ e x)
   have h(t:Test 2)(ht:t∈silver C d) := fixed_moments H (d:=d) p x h₀ ha hh (ℬ e x) t ht
   obtain ⟨B,hB,hV⟩:= determinant H p hn hD hh
   have h' := RateLE.mul (RateLE.const B p.fades.2) (RateLE.sum (S:=silver C d) p.fades.2 (f:=fun t i=>‖P t i‖) fun q hq=>(h q hq).norm)
   have heq := h' (2*a) (by simp only [zero_add]; linarith only [ha'])
   filter_upwards [hV,heq] with i hi hh v hv
   have hz: U i d (Levy.reflect d v)=τ he (ℬ e x):=by
      rw [←bar_shift H x he,←hv]; exact ((p.realism i d hD).reflects (Signed.mirror timeAxis) _) |>.trans (congr_arg _ ((p.realism i d hD).bars _))
   have hP(t:Test 2):payPair H p t i v (Levy.reflect _ v) = P t i :=by
      change scene S d (p.path i) t (U i d v) _=_
      rw [hv,hz]; exact reflects H he _ _ (p.fades.1 i)
   have hv:= norm_nonneg v
   replace hi : ‖v‖^2 ≤ B * (∑ t∈silver C d, ‖P t i‖) := by simpa only [replay,hP] using hi v
   change ‖B*(∑ t∈silver C d, ‖P t i‖)‖ ≤ _ at hh
   rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hh
   rw [mul_assoc, two_mul, Real.exp_add] at hh
   nlinarith only [hv,hi,hh,Real.exp_pos (a*clock i)]

omit h₀ ha he in
include p in
lemma shelf_bijective (earlier:Nonempty (Spin.change S d)) : ∀ᶠ i in atTop,Bijective (U i d):=by
  obtain ⟨B,hB,hV⟩:=determinant H p hn hD hh
  obtain ⟨A⟩:=earlier
  filter_upwards [hV] with i hi
  have hk(v:V d)(hv:p.maps i d v=0) : v=0:=by
     specialize hi v
     have he(t:Test 2): ∀x, payPair H p t i v x=0 := fun x=> by
        change live H p t i (p.maps i d v) _=0
        rw [hv,map_zero,LinearMap.zero_apply]
     simp only [replay,he,norm_zero,Finset.sum_const_zero,mul_zero] at hi
     exact norm_le_zero_iff.mp (by nlinarith only [hi,norm_nonneg v])
  have ht:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hk)
  refine ⟨ht, Function.Surjective.of_comp_left (f:= ⇑A.symm) ?_ A.symm.injective⟩
  exact LinearMap.surjective_of_injective (f:=A.symm.toLinearMap.comp (p.maps i d)) (A.symm.injective.comp ht)

include p h₀ he ha
lemma shelf_uniform (hX:Scaling S)(a :ℝ)(ha':(e:ℝ)<a):∀ᶠ i in atTop, ∀ x:S.Field e, ∀ v: (Bel C.book).Field d, U i d v= τ he x → ‖v‖ ≤ Real.exp (a*(mark p.path i)) * ‖x‖:= by
   obtain ⟨α,hα,h'α⟩:= exists_between ha'
   let B:= Module.finBasis ℂ (S.Field e)
   let A:= ∑ i, ‖(B.coord i).toContinuousLinearMap‖
   filter_upwards [shelf_bijective H p hn hD hh ⟨hX.U 0 d⟩, eventually_all.mpr (fun i=> shelf_inverse_preimage H p (B i) h₀ he hn hD ha hh α hα), (RateLE.const A p.fades.2) ((a:ℝ)-α) (by linarith)] with i hb hi h_A x v hv
   have hi':= hb.1
   choose u h using fun j=> hb.2 (τ he (B j))
   specialize hi' (a₁:=v) (a₂:=∑ j, B.repr x j • u j)
   rw [hi' (hv.trans (by rw [map_sum]; simp_rw [map_smul,h]; simp_rw [← map_smul, ← map_sum,Module.Basis.sum_repr]))]
   calc _ ≤ ∑ j, ‖(B.coord j).toContinuousLinearMap‖ * ‖x‖ * Real.exp (α*(mark p.path i)) :=(norm_sum_le ..).trans (Finset.sum_le_sum fun j hj=> by rw [norm_smul]; exact mul_le_mul ((B.coord j).toContinuousLinearMap.le_opNorm x) (hi j _ (h j)) (norm_nonneg _) (show 0 ≤ ‖(B.coord j).toContinuousLinearMap‖ * ‖x‖ from mul_nonneg (norm_nonneg ((B.coord j).toContinuousLinearMap)) (norm_nonneg x))) -- repair
        _ = A * Real.exp (α*(mark p.path i)) * ‖x‖ := by rw [← Finset.sum_mul,← Finset.sum_mul, mul_right_comm]
        _ ≤ _:=?_ -- price
   have heA : (A:ℝ) ≤ _:= (Real.le_norm_self _).trans h_A
   refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right heA (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; congr 1; ring)) (norm_nonneg _)
end YM.OPE.Coverage

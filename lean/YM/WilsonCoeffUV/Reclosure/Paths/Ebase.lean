import YM.WilsonCoeffUV.Reclosure.Paths.RetainBase
import YM.WilsonCoeffUV.Reclosure.Assemble
import YM.WilsonCoeffUV.Root.Step.OrbitMap
/-!
# Using a prescribed germ measured in Path charges

Packets start at genuine mismatches, CORE transverse affine null once
E2 jets match. Keep exact wraps. No equality hypothesis USED FOR THE THEORY
(future WCU recursion); adapter for supplied p : Bounds + E. No actual error,
origin support or budget recovery when reusing E outputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near Stationary PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{k r t e:ℕ}{s A B a:ℝ}{C:Clip}{R:PathData G}{P:Canvas G}

lemma sand_span (T: SeriesA G) (n:Side): shellK 2 (sands T n):=by
    induction T with
    | nil=> exact fun _ _ _=>rfl
    | cons i T ih=>
      rw [show sands (i::T) n= surf i n+sands T n from rfl]
      intro e t ht; simp only [Pi.add_apply,ih e t ht,add_zero]
      unfold surf; split; · unfold sprig; apply shine_dark; have H:= i.rankA; omega
      rfl
lemma sands_shape (h:0<s)(T:SeriesA G)(p:Draw T s a)(e:ℕ)(n:Side): Pure (sands T n e):=by
    induction T with
    | nil=> exact Pure.zero
    | cons i T ih=>
      rw [show sands (i::T) n= surf i n+sands T n from rfl,Pi.add_apply]; apply Pure.add _ (ih ⟨p.1,fun _ t=> p.2 _ (List.mem_cons_of_mem _ t)⟩)
      unfold surf; split; · exact sprig_pure _ (turns_analytic i.cells h (p.2 i (List.mem_cons_self ..)).toll).contDiffAt _ _
      exact Pure.zero
lemma orb_prism (h:0<s)(i:PrismA G)(p: Commission i.cells s a i.grade)(n:Side):
    rollTest (flash (surf i n)) (flash (surf i n)) 1 0:=by
    let t:=i.rise+2; let f:=turnSeries i.cells (m:=n)
    have he:Green f:= (turns_analytic i.cells h p.toll).contDiffAt
    let w:=sprig f t
    have hx:rollTest (flash w) (flash w) 1 0:=by
       have hf:PowerSeries.X^t*flash w=jet f:=by
           apply moves; intro k ht
           rw [jet_apply, show rye f k=0 from ?_,map_zero]; ext1 x
           unfold rye; rw [(rays_jet he.analyticAt t).1 (turns_low i.cells h p.toll) k ht]; simp
       intro Z _ q X X' v; apply mul_left_cancel₀ (a:=(PowerSeries.X :Blue.Ink Z)^t) (pow_ne_zero _ X_ne_zero)
       conv_lhs=>arg 1; arg 1; rw [← train_X (Blue.spool X)]
       conv_rhs=>arg 1; arg 1; rw [← train_X (Blue.spool X')]
       rw [← map_pow,← map_pow, ← map_mul,← map_mul,hf,traveling _ v.g₀ v.f₀ _ he,traveling _ v.g₁ v.f₁ _ he]
       apply jet_congr; filter_upwards [v.shift] with t ht; unfold f; simp only [Function.comp_apply,turnSeries, Patch.average,mantle_input]; simp_rw [ht,Lattice.pull_id,Work.F05.pull_gauge_zero,Work.F05.uncut_gauge i.cells p.hue]
    rw [show flash (surf i n)=PowerSeries.X^i.grade * flash w from ?_]; swap
    · apply PowerSeries.ext; intro j; rw [coeff_X_pow_mul',Blue.flash,coeff_mk]; unfold surf; split; · simp only [w,f,t,Blue.flash,coeff_mk]
      simp [totalR]
    intro Z _ q X X' H; rw [map_mul,map_pow,train_X,map_mul,map_pow,train_X,hx H]
lemma orbit_sumT {P Q:PChart G c}(h:shellK 2 P)(p:shellK 2 Q)(v:rollTest (flash P) (flash P) 1 0)(t:rollTest (flash Q) (flash Q) 1 0) : rollTest (flash (P+Q)) (flash (P+Q)) 1 0:=by rw [flash_add (finite_shell h) (finite_shell p)]; intro Z _ q X X' g; rw [map_add,map_add,v g,t g]
lemma sand_orbit (h:0<s)(T:SeriesA G)(p:Draw T s a)(n:Side): rollTest (flash (sands T n)) (flash (sands T n)) 1 0:=by
   induction T with
   | nil=> intro Z _ q X X' H; rw [show Blue.flash (sands ([]:SeriesA G) n)=0 from ?_, map_zero,map_zero]; ext1 j; simp only [Blue.flash,coeff_mk,map_zero]; simp [sands,totalR]
   | cons i T ih=> rw [show sands (i::T) n=surf i n+sands T n from rfl]; exact orbit_sumT (by have he:= sand_span [i] n; rw [show sands [i] n=surf i n from by simp [sands]] at he; exact he) (sand_span _ _) (orb_prism h i (p.2 _ (List.mem_cons_self ..)) n) (ih ⟨p.1,fun _ t=>p.2 _ (List.mem_cons_of_mem _ t)⟩)
lemma stance (K:R.Bounds C s A B)(n:Side): shellK 2 (front R C n):=by
    intro e t ht; rw [front_full K n]; simp_rw [Pi.add_apply,Pi.smul_apply,sand_span _ _ _ _ ht, sprig_count (eWilson (G:=G) (c:=n)) 2 e t ht,smul_zero,add_zero]
lemma shape_c (K:R.Bounds C s A B)(e:ℕ)(n:Side): Pure (front R C n e):=by
    rw [front_full K n,Pi.add_apply,Pi.smul_apply]; exact Pure.add (fun r=>(sprig_pure (eWilson (G:=G) (c:=n)) W_green 2 e r).smul C.direct) (sands_shape K.width _ (tide_chart K) _ _)
lemma orbFront (K:R.Bounds C s A B)(n:Side): rollTest (flash (front R C n)) (flash (front R C n)) 1 0:=by
    rw [front_full K n]; refine orbit_sumT ?_ (sand_span _ n) (@?orb) (sand_orbit K.width _ (tide_chart K) n)
    · intro i r h; simp only [Pi.smul_apply,sprig_count (eWilson (G:=G) (c:=n)) 2 i r h,smul_zero]
    let s:=sprig (eWilson (G:=G) (c:=n)) 2
    have he:rollTest (flash s) (flash s) 1 0:=top_turn (H:=unitRow (TypeFace 2)) (acts_unit n) 1 0
    rw [Soil.flash_mu C.direct (sprig_count _ 2)]
    intro Z _ q X X' v; rw [train_smul,train_smul,he v]
lemma frontr (K:R.Bounds C s A B)(e r n): front R C n e (r+1)= lagoon (breast R C e (r+1)) n:=by
    rw [front_full K n]; unfold breast; simp only [Pi.add_apply,Pi.smul_apply,wraps_signed K.width (pool R) (tide_chart K),moon_wrap]
    have hZ:0<steep s:= div_pos K.width (by norm_num)
    obtain ⟨T,ht⟩:= moon_bill G e (r+1) 1 zero_le_one
    rw [lagoon_plus (ht.smul _) (huesT_bill hZ.le (pollen_sum K.width (tide_chart K) e (r+1))) one_pos hZ, lagoon_scalar]

lemma moon_sign (G:Gauge)(k r:ℕ)(s:Signed)(x: Fin r→ YForest G) : moon G k r (tickW s 0 ∘ x)= veil x s*moon G k r x:=by
    let H (n:Side):=sprig (eWilson (G:=G) (c:=n)) 2
    let h:= moon_pages G k r
    apply tendsto_nhds_unique (h.point (tickW s 0 ∘ x)); have he := ((moon_pages G k r).point x).const_mul (veil x s)
    refine he.congr (fun n=>?_)
    have hz := signed_pair (P:=H n) (P':=H n) (top_turn (H:=unitRow (TypeFace 2)) (acts_unit n) s 0) (sprig_count _ 2) (sprig_count _ 2) (sprig_pure _ W_green 2) (sprig_pure _ W_green 2) k r (foldUnder n ∘ x)
    rw [show foldUnder n ∘ (tickW s 0 ∘ x)=toss G s 0 ∘ foldUnder n ∘ x from funext fun i=>target0 ..]
    change H _ _ _ _=veil x s*H _ _ _ _ at hz
    change veil _ _*dilute (fun j=>H j k r) n _=dilute (fun j=>H j k r) n _; unfold dilute; split<;>rename_i he
    · simp only [Pi.smul_apply,hz,smul_eq_mul]; ring
    exact hz.symm
lemma breast_axis (_:R.Bounds C s A B)(e r s' x): breast R C e r (tickW s' 0 ∘ x)= veil x s' * breast R C e r x:=by
    unfold breast; simp only [Pi.add_apply,Pi.smul_apply,moon_sign,huesT_axis]; ring
lemma breast_stroll (K:R.Bounds C s A B)(e r):stroll (breast R C e r):=by
    intro b x; unfold breast; simp only [Pi.add_apply,Pi.smul_apply, (moon_pages G e r).road b x,(huesT_stroll ((soul K.width (tide_chart K) e).hike r) b x)]
lemma breast_nil (K:R.Bounds C s A B)(e r)(h:r≤1 ∨ e+2<r) : breast R C e r=0:=by
    unfold breast; simp only [Pi.add_apply,Pi.smul_apply, (soul K.width (tide_chart K) e).nilV r h]
    rw [show moon G e r=0 from ?_,huesT_zero]; simp
    apply (moon_pages G e r).unique; apply Yields.zero.congr (Eventually.of_forall (fun n=>?_)); unfold sprig; rw [shine_dark (by omega)]; rfl
lemma frontFee (K:R.Bounds C s A B) (e r): ∀ x:ℝ, Amber Bank.terrain (steep s) x (moon G e r) → Amber Bank.terrain (steep s) (C.direct*x+(pool R).length*((A+B+gramCost G A)*Mosaic.tax G s e) * Real.exp (2*steep s)) (breast R C e r):=by
    have hh:=huesT_bill (div_pos K.width (by norm_num)).le (pollen_sum K.width (tide_chart K) e r)
    intro x v
    exact (by simpa only [abs_of_nonneg C.quadratic_pos.le] using! ((v.smul C.direct).add hh))
lemma breast_turn (K:R.Bounds C s A B)(e r): Yields (fun n=>front R C n e r) (breast R C e r):=by
    cases r with
    | zero=> rw [breast_nil K e 0 (by omega)]; refine Yields.zero.congr ?_
             apply Eventually.of_forall; intro n; rw [front_full K n]; simp only [Pi.add_apply,Pi.smul_apply,sands_zero_v]; rw [sprig, shine_dark (by omega)]; simp
    | succ r=> have hv:0<steep s:=div_pos K.width (by norm_num)
               obtain ⟨z,hz⟩:= moon_bill G e (r+1) (steep s) hv.le
               exact (lagoon_yields (frontFee K e (r+1) z hz) hv (breast_stroll K e (r+1))).congr (Eventually.of_forall fun n=> (frontr K e r n).symm)
lemma frontage (K:R.Bounds C s A B)(e:ℕ): PointV (breast R C) e:=by
    let F:=front R C; let X:=breast R C
    have he:=breast_turn K
    exact ⟨riseV F X he (orbFront K) (fun n e=>shape_c K e n) (stance K) e,fun r=>(he e r).sym (Eventually.of_forall fun n=>shape_c K e n r), breast_stroll K e, fun r=>mural_sigma F X (orbFront K) (stance K) (fun n e=>shape_c K e n) _ _ (he e r), breast_nil K e⟩
lemma front_dark (_:R.Bounds C s A B)(h:3≤ e): breast R C e 2=0:=by
    rw [breast]; simp only [Pi.add_apply,Pi.smul_apply]
    have he:moon G e 2=0:= (moon_pages G e 2).unique (Yields.zero.congr (Eventually.of_forall (fun n=> Eq.symm (shine_dark (by omega)))))
    have hx: fromBefore (pool R) e:=by intro i hi; simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with p|p|p|p<;> subst i<;>  simp <;> omega
    rw [he,empty_two hx,huesT_zero]; simp

-- extend from any through cutoff I≤E all. e steps. Stronger Than AUTH salt.
lemma uncoil (G:Gauge)(e m:ℕ)(s:ℝ)(hs:0<s): ∃ (v C:ℝ), 0<v ∧ v≤ s ∧ 0≤ C ∧∀ (F:Canvas G) a,0 ≤ a → (∀ i<m,F i=0) → (∀ i, m ≤ i → i<m+e → Desc F i s a) → ∃ P:SeriesA G, (∀ i∈P,m ≤ i.grade)∧ fromBefore P (m+e) ∧ sews P F (m+e) ∧ P.length ≤ meterPre (m+e) ∧Draw P v (a*C):=by
    induction e with
    | zero=> exact ⟨s,0,hs,le_rfl,le_rfl,fun F a _ h _=>⟨[],by simp,by simp [fromBefore],fun i hi=> (h i hi).symm,Nat.zero_le _,draw_nil (by simp)⟩⟩
    | succ e ih=>
      obtain ⟨v',C,hv,hp,hC,H⟩:= ih
      -- use direct Halo argument to keep grades
      let d:=m+e; let t:=steep v'; have ht:0<t:= div_pos hv (by norm_num)
      have hh:t≤ v':=by unfold t steep; linarith
      obtain ⟨v,Q,hv',hq,hQ,q⟩:=sprocket G d (d+1) le_rfl t ht
      let K:ℝ:= meterPre d*(C*Mosaic.tax G v' d)
      have hz : 0≤ K:= mul_nonneg (by positivity) (mul_nonneg hC (tax_nn G hv d))
      refine ⟨v,C+Q*(1+K),hv',hq.trans (hh.trans hp),by positivity,?_⟩; intro F a ha hf he
      obtain ⟨P,y,w,o,b,l⟩:= H F a ha hf (fun i j k=>he i j (by omega))
      let T:= F-murals P
      have he': Desc F d s a:= he d (by omega) (by omega)
      have hy:T d 2=F d 2:=by unfold T; rw [Pi.sub_apply,Pi.sub_apply,empty_two w,sub_zero]
      have hg:T d 2=F d 2:=hy
      have heT:Desc T d t (a+a*K):=by
         constructor
         · exact he'.toPointV.sub (soul hv l d)
         · intro r; apply (((he'.beats r).mono (hh.trans hp)).sub (pollen_sum hv l d r)).le
           apply add_le_add_right; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr b) (mul_nonneg (mul_nonneg ha hC) (tax_nn G hv d))).trans_eq (by unfold K; ring)
         · rw [hy]; exact he'.sign
         rw [hy]; exact he'.aft
      obtain ⟨V,vV⟩:= q T (a+a*K) (by positivity) heT (fun i hi=>by simp only [T,Pi.sub_apply, o i hi, sub_self])
      have hd : m+(e+1)=d+1:= rfl; rw [hd]; refine ⟨P++V, fun i hi=>(List.mem_append.mp hi).elim (y i) (fun j=>by rw [(vV.same i j).1]; omega),fromBoth _ _ (fun i j=>(w _ j).trans (by omega)) (fun i j=>by rw [(vV.same i j).1]; omega), fun i j=>?_,by rw [List.length_append, meterPre,vV.lim]; exact Nat.add_le_add_right b _,?_⟩
      · rw [murals_append,Pi.add_apply]; by_cases h:i=d; subst i; rw [extHalo hv' vV heT.toPointV]; unfold T; rw [Pi.sub_apply]; abel
        rw [silence_m vV.same (by omega),o i (by omega), add_zero]
      have hz' :0≤ Q*(1+K):=by positivity
      exact (l.light (hq.trans hh) (mul_le_mul_of_nonneg_left (by linarith) ha)).both (vV.light.light le_rfl (by nlinarith only [mul_nonneg ha hC]))

-- fixed order price before block choices (geometry v after s). Input Size from FIRST stakes; L may get this at post but no inheritance needed. Requires same prescription.
lemma front_price (G:Gauge)(e:ℕ){s:ℝ}(he:0<s): ∃ c':ℝ,0≤c'∧∀ (R:PathData G)(C:Clip)(A B:ℝ), R.Bounds C s A B → ∀ i, i<e →∀ r, Amber Bank.terrain (steep s) (c'*(C.direct+A+A*A+B)) (breast R C i r):=by
    have h i r :=moon_bill G i r (steep s) (div_pos he (by norm_num)).le
    let c:ℝ:= Fintype.card PlaqAxes*(Fintype.card G.ColorIndex/2:ℝ)
    let U i r:= (h i r).choose+4*Mosaic.tax G s i*(1+c)*Real.exp (2*steep s)
    let a:= ∑ i ∈ Finset.range e,∑ r∈ Finset.range (e+3), U i r
    have hv:0≤ c:=by unfold c; positivity
    have hp i r:= (h i r).choose_spec.1; have hE:0 ≤ Real.exp (2*steep s):=by positivity
    have hz i r:0≤ U i r:= add_nonneg (hp i r) (mul_nonneg (mul_nonneg (by have hb:=tax_nn G he i; positivity) (by linarith)) hE)
    have ha:0≤ a:= Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=>hz _ _
    refine ⟨a,ha,?_⟩; intro R C A B K i h' r
    have ht:= C.quadratic_pos; have hT:= cap_nn K.three; have hl:= cap_nn K.two; have hh :0≤ C.direct+A+A*A+B:= by positivity
    by_cases H:e+2<r
    · rw [breast_nil K i r (by omega)]; exact Amber.zero.le (by positivity)
    have ht': A+B+gramCost G A≤(1+c)*(C.direct+A+A*A+B):=by
        rw [show gramCost G A=c*(A*A) from ?_]; swap; · unfold gramCost c; ring
        nlinarith [mul_nonneg (add_nonneg (add_nonneg ht.le hT) hl) hv]
    have hV : U i r ≤ a := (Finset.single_le_sum (f:= U i) (fun j _=> hz i j) (Finset.mem_range.mpr (by omega:r<e+3))).trans (Finset.single_le_sum (f:=fun i=>∑ r∈Finset.range (e+3),U i r) (fun i _=> Finset.sum_nonneg fun r _=>hz i r) (Finset.mem_range.mpr h'))
    apply (frontFee K i r _ (h i r).choose_spec).le; refine le_trans ?_ (mul_le_mul_of_nonneg_right hV hh)
    have hx:= tax_nn G he i
    calc
      _ ≤ (C.direct+A+A*A+B)*(h i r).choose + (4:ℕ)*((1+c)*(C.direct+A+A*A+B)*Mosaic.tax G s i)*Real.exp (2*steep s):= add_le_add (mul_le_mul_of_nonneg_right (by nlinarith) (hp i r)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht' hx) (by positivity : 0≤((4:ℕ):ℝ))) hE)
      _ = _:= by unfold U; norm_cast; ring

-- E comparison must prove this EXACT or with appropriate losses & controlled transport, not EBU
structure SeamPhase (C:Clip)(R:PathData G) (P:Canvas G) : Prop where
    low i: i<3 → breast R C i =P i

def sandLift (P:SeriesA G): Canvas G:= fun e r=> huesT (murals P e r)

/-- If the constructions' prior analytic path reps (E label charges) are retained.
New unmarked packets through every finite order, *after signing*, and no new
grades through first prescribed 0,1,2. Seals inherited orientation
channels. Use for the given unmasked germs only, not as E representative
controls. No comparison or agreement of those low orders provided here.
-/
theorem circled (G:Gauge)(e:ℕ){s:ℝ}(he:0<s): ∃ v c', 0<v∧v≤s∧0≤c'∧∀ (R:PathData G)(C:Clip)(P:Canvas G) (A B a:ℝ),0≤ a → R.Bounds C s A B → SeamPhase C R P →
    (∀ i, i<3+e → Desc P i s a ∧ (∀ r s x,P i r (tickW s 0 ∘ x)=veil x s * P i r x)) →
    ∃ X:SeriesA G,(∀ i∈X,3 ≤ i.grade) ∧ fromBefore X (3+e) ∧ X.length ≤ meterPre (3+e) ∧ Draw X v (c'*(C.direct+A+A*A+B+a)) ∧
       ∀ i, i<3+e → (breast R C+ sandLift X) i=P i ∧ ∀ n:Side, ∀ r, (front R C n+sands X n) i (r+1)= lagoon (P i (r+1)) n:=by
    let t:= steep s; have h':0<t:= div_pos he (by norm_num); have ht:t≤s:=by unfold t steep; linarith
    obtain ⟨c,hc,f⟩:=front_price G (3+e) he; obtain ⟨v,B,hv,hp,hB,Q⟩:=uncoil G e 3 t h'
    refine ⟨v,B*(1+c),hv,hp.trans ht,by positivity,?_⟩; intro R C P A B' a ha K H h
    let E:=C.direct+A+A*A+B'; let F:=P-breast R C
    have hh:=cap_nn K.two; have hq:=cap_nn K.three; have hhE:= C.quadratic_pos; have hE:0≤E:=by unfold E; positivity
    have Hs i (p:i<3+e) r s x: F i r (tickW s 0 ∘ x)=veil x s*F i r x:=by simp only [F,Pi.sub_apply,(h _ p).2 r s, breast_axis K,mul_sub]
    have hF i (p:3 ≤ i)(z:i<3+e): Desc F i t (a+c*E):=by
       have hy:F i 2=P i 2:=by unfold F; rw [Pi.sub_apply,Pi.sub_apply,front_dark K p,sub_zero]
       refine ⟨(h _ z).1.toPointV.sub (frontage K i),fun r=> (((h _ z).1.beats r).mono ht).sub (f R C A B' K i z r), by rw [hy]; exact (h _ z).1.sign,by rw [hy]; exact (h _ z).1.aft⟩
    obtain ⟨X,h₁,h₂,h₃,h₄,h₅⟩:= Q F (a+c*E) (by positivity) (fun i p=>by simp only [F,Pi.sub_apply,H.low i p,sub_self]) hF
    refine ⟨X,h₁,h₂,h₄,h₅.light le_rfl ?_,?_⟩
    · change _≤ B*(1+c)*(E+a); nlinarith [mul_nonneg hB hE,mul_nonneg (mul_nonneg hB hc) ha]
    intro i p; have hx:(breast R C+sandLift X) i=P i:= by
       funext r; rw [Pi.add_apply, Pi.add_apply,sandLift,h₃ i p,huesT_same (Hs i p r)]; unfold F; rw [Pi.sub_apply,Pi.sub_apply]; abel
    refine ⟨hx,fun n r=>?_⟩
    rw [Pi.add_apply,Pi.add_apply,frontr K _ _ n,wraps_signed hv X h₅,← hx]; change _= lagoon (_+huesT _) n
    rw [lagoon_plus (f R C A B' K i p (r+1)) (huesT_bill _ (pollen_sum hv h₅ i (r+1))) h' (div_pos hv (by norm_num))]; exact (div_pos hv (by norm_num)).le
end YM.WilsonCoeffUV.Bank.Mosaic

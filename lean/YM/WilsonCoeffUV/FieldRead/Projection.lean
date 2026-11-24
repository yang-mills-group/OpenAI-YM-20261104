import YM.WilsonCoeffUV.Test.Axis
import YM.WilsonCoeffUV.Vacuum.UV.LimitGauge
import YM.Planned.PRIMARY_INTEGRAL_295.Twists
import YM.Planned.PRIMARY_INTEGRAL_295.Bigrade

/-!
# Π of potential tensors, reading log hol and continuous test. Unwrapped.
These are color-real. Labels later with real form binding Stamp.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 45000
noncomputable section
namespace YM.WilsonCoeffUV.Fountain
open Filter Function Set Laurent Lattice RG Exterior Precision Next.Free Gauge Matrix Work.F08
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l m p:ℕ}{A C s t :ℝ}

abbrev Fane (G:Gauge)(h l:ℕ) := Tensor.T (Snap G h) ℝ l
abbrev ChamberTen (G:Gauge)(V:Type*)(r:ℕ):= Ten V (YForest G) r

-- whole anchor budget from Twig, allow r=0 and trivial Gauge
lemma shrub (V:Type*)[NormedAddCommGroup V](F:ChamberTen G V r)(g:Twig 0 s A F)(h:t<s)(k:ℕ): SumBudget (fun x=> ((1+(port_d 0 x):ℝ)^k*Real.exp (t*port_d 0 x))*‖F x‖) ((A*ceilPoly k ((s-t)/2))*tiePay (Hooks G) r ((s-t)/2)):=by
   classical
   by_cases hs:Nonempty (Hooks G)
   · let v:YForest G:= (0,Classical.choice hs)
     let Z:ChamberTen G V (r+1):=fun y=> if y 0=v then F (Fin.tail y) else 0
     have he: Amber Bank.terrain s A Z:= by
        refine ⟨g.1,fun x=>?_⟩; unfold Z; let p:=g.1; split
        next hv =>
           have hx : soar Bank.terrain x = port_d 0 (Fin.tail x):= by
               conv_lhs=> rw [←Fin.cons_self_tail x,hv]
               exact port_soar ..
           rw [hx]; exact g.2 (Fin.tail x)
        next => rw [norm_zero]; positivity
     have hu:=cent_amber he h v k; unfold cent at hu
     simp_rw [port_soar] at hu; simpa [Z] using hu
   have hr := not_nonempty_iff.mp hs
   by_cases he:r=0
   · subst r; have H : Finite (Fin 0 → YForest G):= inferInstance
     let u:Fin 0 → YForest G:= Fin.elim0
     have hp (x:Fin 0→YForest G):port_d 0 x=0:= Nat.le_zero.mp (league_le Bank.terrain _ (fun i j=>by rw [show i=j from (by omega)]; exact Nat.le_of_eq (Bank.terrain.self _)))
     simp_rw [hp]; have hb : ‖F u‖≤ A:=by simpa [hp] using g.2 u
     have ha : 1≤ ceilPoly k ((s-t)/2):= by simpa using ceilPoly_use k (by linarith :0 < (s-t)/2) 0
     simp only [Nat.cast_zero,add_zero,one_pow,mul_zero,Real.exp_zero,one_mul,tiePay,pow_zero,mul_one]
     exact ⟨fun _=> norm_nonneg _, summable_of_hasFiniteSupport (Set.toFinite _), by rw [tsum_eq_single u (fun _ w=> False.elim (w (Subsingleton.elim ..)))]; exact hb.trans (le_mul_of_one_le_right g.1 ha)⟩
   haveI : IsEmpty (Fin r→YForest G):= IsEmpty.mk fun x=> isEmptyElim (x ⟨0,Nat.pos_of_ne_zero he⟩).2
   have hp:= g.1; have hc:0≤ceilPoly k ((s-t)/2):= (ceilPoly_pos ..).le
   exact ⟨fun i=>isEmptyElim i,summable_of_hasFiniteSupport (Set.toFinite _),by rw [tsum_empty]; apply mul_nonneg (by positivity); have hp:= sub_pos.mpr h; exact pow_nonneg (boardPay_nn (by positivity)) _⟩

def feather (x:YForest G):= (x.1,axisEquiv.symm x.2.1)
lemma feather_at (x:Edge Cover)(v:G.ColorIndex): feather (stone x v)=x:=by simp [feather,stone,←coord_map]

def colorL (j:G.ColorIndex) : G.Color→L[ℝ]ℝ := LinearMap.toContinuousLinearMap {
                                                                                  toFun x:= x j
                                                                                  map_add' _ _:=rfl
                                                                                  map_smul' _ _:= rfl }

def flex (x:YForest G)(X: Snap G h): ℝ:= Film.lane (seat x.1) (feather x).2 X x.2.2
lemma flex_smooth (x:YForest G) : ContDiffAt ℝ ω (flex (h:=h) x) 0:=by
    let T:G.Color→L[ℝ]ℝ:=colorL x.2.2
    exact T.contDiff.contDiffAt.comp (0:Snap G h) (Film.lane_smooth ..)
lemma flex_zero (x:YForest G):flex (h:=h) x 0=0:=by rw [flex,Film.lane_root]; rfl

def mite (u: Fin r→YForest G)(X: Snap G h): ℝ:= ∏ i,flex (u i) X
private lemma pprod {X ι:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] (S:Finset ι)(F:ι→X→ℝ)(x:X)(n:WithTop ℕ∞)(h:∀ i∈ S,ContDiffAt ℝ n (F i) x):ContDiffAt ℝ n (fun a=> ∏ i∈S,F i a) x:=by
    classical
    induction S using Finset.induction_on with
    | empty=>simp; exact contDiffAt_const
    | insert i S hi ih => simp_rw [Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).mul (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma mite_smooth (u: Fin r→YForest G): ContDiffAt ℝ ω (mite (h:=h) u) 0:= pprod Finset.univ (fun i=>flex (u i)) _ _ fun _ _=> flex_smooth ..

abbrev Cart (G:Gauge)(h:ℕ) := Fin (Module.finrank ℝ (Snap G h))
def casing (G:Gauge)(h:ℕ) : (Snap G h) ≃L[ℝ] Lawn (Cart G h):= (Module.finBasis ℝ (Snap G h)).equivFun.toContinuousLinearEquiv
abbrev Glas (G:Gauge)(h l:ℕ) := Tensor.T (Lawn (Cart G h)) ℝ l

def skyline (h)(u:Fin r→ YForest G)(l) : Glas G h l:= Tensor.coeff (mite u ∘ (casing G h).symm) l 0
lemma skyline_auth (h)(u:Fin r→YForest G)(l): Tensor.Sym (skyline h u l):= by
    apply Tensor.coeff_symm
    have H := ((mite_smooth (h:=h) u).of_le (show (l:WithTop ℕ∞)≤ω from le_top)); exact ((map_zero (casing G h).symm).symm ▸ H).comp 0 (casing G h).symm.toContinuousLinearMap.contDiff.contDiffAt
private def lure (u:Fin r→YForest G): Snap G h→L[ℝ](Fin r→EdgeRead G h) := ContinuousLinearMap.pi fun i=> Film.sampleIn (seat (u i).1) (feather (u i)).2
private lemma tug (x : Cover)(i:Axis)(a:Snap G h): ‖Film.sampleIn (Place.seat x) i a‖ ≤ liftCost h x * ‖a‖:=by
    let P : Snap G h→L[ℝ]Route G h:=road (Place.seat x) i
    change ‖((0:G.Color),(0:G.Color), P a)‖ ≤ _
    have he := ((road (G:=G) (d:=h) (Place.seat x) i).le_opNorm a).trans (mul_le_mul_of_nonneg_right (Film.road_cap x i) (norm_nonneg _))
    rw [Prod.norm_def, Prod.norm_def]; rw [max_le_iff,max_le_iff]; exact ⟨(by rw [norm_zero]; exact mul_nonneg (liftCost_pos ..) (norm_nonneg _)), (by rw [norm_zero]; exact mul_nonneg (liftCost_pos ..) (norm_nonneg _)),he⟩
lemma port_size (u: Fin r→ YForest G)(i:Fin r): size (u i).1≤port_d 0 u:= by
    have he:= leg_le Bank.terrain (Fin.cons 0 (Prod.fst ∘ u)) 0 (Fin.succ i)
    change size ((u i).1-(0:Cover))≤_ at he; simpa [port_d] using he
private lemma casing_pay (G:Gauge)(h:ℕ): ∃ M:ℝ,0≤ M ∧ ∀ i, ‖(casing G h).symm i‖ ≤ M*‖i‖:= by
    let V: Lawn (Cart G h) →L[ℝ] Snap G h:= (casing G h).symm.toContinuousLinearMap
    exact ⟨‖V‖,norm_nonneg V,fun i=> V.le_opNorm i⟩
private lemma billhook (u:Fin r→YForest G): ‖(lure u).comp (casing G h).symm.toContinuousLinearMap‖ ≤ (1+port_d 0 u:ℝ)^h * (casing_pay G h).choose:=by
    obtain ⟨hx,hv⟩ := (casing_pay G h).choose_spec
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro a; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=> ?_
    let F : Snap G h→L[ℝ] EdgeRead G h:= Film.sampleIn (Place.seat (u i).1) (feather (u i)).2
    change ‖F _‖ ≤ _; apply (tug (u i).1 (feather (u i)).2 ((casing G h).symm a)).trans; rw [mul_assoc]; apply mul_le_mul _ (hv a) (norm_nonneg _) (by positivity); unfold liftCost; gcongr; exact port_size ..
lemma tune (G:Gauge)(h r l:ℕ): ∃ C:ℝ,0 ≤ C ∧ ∀ u:Fin r→ YForest G, ‖skyline h u l‖≤ C*(1+port_d 0 u:ℝ)^(h*l):=by
    let S (j:Fin r→G.ColorIndex)(Z:Fin r→EdgeRead G h):ℝ := ∏ i, logo (Z i) (j i)
    let W j := iteratedFDeriv ℝ l (S j) 0
    let c:ℝ := (l.factorial:ℝ)⁻¹
    let C := (casing_pay G h).choose; have hx:0≤C:= (casing_pay G h).choose_spec.1
    refine ⟨c*((∑ j,‖W j‖)*C^l),by unfold c; positivity,fun u=>?_⟩
    let j:=fun i=>(u i).2.2
    have H : ContDiffAt ℝ (↑l) (S j) 0:= by
        unfold S
        apply pprod; intro i _
        let L:G.Color→L[ℝ]ℝ:= colorL (G:=G) (j i)
        exact ((L.contDiff.contDiffAt.comp (0:EdgeRead G h) ((logo_smooth ..).of_le le_top)).comp (0:Fin r→EdgeRead G h) (contDiffAt_apply ℝ ..))
    let g:=(lure u).comp (casing G h).symm.toContinuousLinearMap
    change ‖c • iteratedFDeriv ℝ l (S j ∘ g) 0‖ ≤ _
    rw [Next.Foundations.jets_linear _ H,norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0≤c by unfold c; positivity),mul_assoc]
    apply mul_le_mul_of_nonneg_left ?_ (by unfold c; positivity); apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..)
    rw [mul_assoc, mul_comm (C^l)]
    apply mul_le_mul (Finset.single_le_sum (fun i _=>norm_nonneg (W i)) (Finset.mem_univ j)) _ (Finset.prod_nonneg fun _ _=> norm_nonneg _) (Finset.sum_nonneg fun _ _=>norm_nonneg _)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin, pow_mul]; rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (billhook u) _

def arret (c:Volume D)(F:ChamberTen G (Vote D) r) (h l:ℕ): Glas G h l:= ∑' v, (F v c) • skyline h v l

def plaud (G:Gauge)(h s r l):= (tune G h r l).choose*(ceilPoly (h*l) (s/2)*tiePay (Hooks G) r (s/2))
lemma arret_bill (c:Volume D)(F:ChamberTen G (Vote D) r) (h l:ℕ)(hc:Twig 0 s A F)(he:0<s): SumBudget (fun v=> ‖(F v c) • skyline h v l‖) (plaud G h s r l*A*‖c‖):=by
    let k:= (tune G h r l).choose
    have hp:0≤k:= (tune G h r l).choose_spec.1
    have hx := shrub _ _ hc he (h*l); simp only [sub_zero, zero_mul, Real.exp_zero,mul_one] at hx
    unfold plaud; rw [show _ *A*‖c‖= k*‖c‖*((A*ceilPoly (h*l) (s/2))*tiePay (Hooks G) r (s/2)) from by unfold k; ring]; refine budget_minor (cap_scale hx (show 0≤k*‖c‖ by positivity)) ?_ (fun v=>?_)
    · intro v; exact norm_nonneg ((F v c) • skyline h v l)
    rw [norm_smul]; exact (mul_le_mul ((F v).le_opNorm _) ((tune ..).choose_spec.2 v) (norm_nonneg _) (by positivity)).trans_eq (by unfold k; ring)
lemma arret_cost (c:Volume D)(F:ChamberTen G (Vote D) r)(h l:ℕ)(hc:Twig 0 s A F)(he:0<s): ‖arret c F h l‖≤plaud G h s r l*A*‖c‖:= let H:=arret_bill c F h l hc he; (norm_tsum_le_tsum_norm H.2.1).trans H.2.2
lemma arret_pays (c:Volume D)(F:ChamberTen G (Vote D) r)(h l:ℕ)(hc:Twig 0 s A F)(he:0<s) (x:Fin l → Lawn (Cart G h)): arret c F h l x= ∑' v,(F v c)*skyline h v l x := (ContinuousMultilinearMap.apply ℝ _ ℝ x).map_tsum ((arret_bill c F h l hc he).2.1.of_norm)
lemma arret_seal (c:Volume D)(F:ChamberTen G (Vote D) r)(h l:ℕ)(hc:Twig 0 s A F)(he:0<s): Tensor.Sym (arret c F h l):= by intro x σ; simp_rw [arret_pays c F h l hc he]; exact tsum_congr fun v=> congr_arg ((F v c)*·) (skyline_auth h v l x σ)
end YM.WilsonCoeffUV.Fountain

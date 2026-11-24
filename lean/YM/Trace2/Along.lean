import YM.Trace2.Shear
import YM.PertExtension.UVBranch

/-! Leading unselected shear/scalar tests in the actual weak frames. No mixing
assumption needed and the tests work on thickened dilation windows. Windows
are cofinal but not assured to cover the entire UV. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Trace
open Function Filter Set Table Spec Analysis Points Maxwell Climb Next.UVStress PertExtension
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C : Family G} {S:Table C.book} {F : Extraction.Order}
local notation "E" => Bel C.book
open Classical Complex WithLp
abbrev raw4 (S:Table C.book) := (E).Field 4 →ₗ[ℂ] S.Field 4
lemma first_custom {d e:ℕ}{v:S.Field e}{w:S.Field d}(x:Points 2) : custom x v w=
    Ward.disc (Fin.cons ⟨e,v⟩ (fun _:Fin 1=>⟨d,w⟩)) x:=rfl
lemma custom_self {e:ℕ}(v:S.Field e)(x:Points 2) : custom x v v =
    Ward.disc (fun _ : Fin 2=>⟨e,v⟩) x:= by rw [first_custom, show Fin.cons (α:=fun i : Fin 2=>S.Tag) ⟨e,v⟩ (fun _:Fin 1=>⟨e,v⟩)=fun _=>⟨e,v⟩ from funext (Fin.cases rfl (fun _=>rfl))]
lemma cu_linear₂ {d e:ℕ}{v:S.Field e}(x:Points 2) :∃ L:S.Field d →ₗ[ℂ]ℂ, ∀ w:S.Field d, custom x v w=L w:=by
   let k:=(fun w:S.Tag=> update (Fin.cons (α:=fun _:Fin 2=>S.Tag) ⟨e,v⟩ (fun _:Fin 1=>⟨d,(0:S.Field d)⟩)) 1 w)
   refine ⟨Ward.here (Fin.cons ⟨e,v⟩ (fun _:Fin 1=>⟨d,(0:S.Field d)⟩)) x 1 d,fun w=>?_⟩
   rw [Ward.takes]; apply congrArg (Ward.disc · x)
   change Fin.cons (α:=fun _:Fin (1+1)=>S.Tag) ⟨_,v⟩ (fun _=>⟨_,w⟩)=k ⟨_,w⟩
   funext i; fin_cases i
   · apply Eq.symm (update_of_ne (f:=Fin.cons (α:=fun _:Fin (1+1)=>S.Tag) ⟨e,v⟩ (fun _:Fin 1=>⟨d,0⟩)) (a':=1) (a:=0) (v:=⟨d,w⟩) (show (0:Fin (1+1))≠1 by decide))
   exact (update_self (α:=Fin (1+1)) (β:=fun _ => S.Tag) (1:Fin (1+1)) (⟨_,w⟩  : S.Tag) _).symm
lemma unit_right_read (s:S.Hierarchy){d e:ℕ}{v:S.Field e}(x:Points 2)(hx:x∈conf _): custom x v (S.unit d)=first_value e v:=by
   obtain ⟨a,ha⟩:=S.onto _ v
   let B:= S.project e a
   change custom x v (S.project d (C.book.scalar d))= _
   rw [← ha]; unfold custom first_value
   let y: Fin 2→C.book.Token:= Fin.cons ⟨e,a⟩ (fun _:Fin 1=>C.book.one d)
   have hF : (S.classTokens ∘ y) = Fin.cons (α:=fun _:Fin 2=> S.Tag) ⟨e,S.project _ a⟩ (fun _:Fin 1=> ⟨d,S.project d (C.book.scalar d)⟩):= funext (Fin.cases rfl (fun _=>rfl))
   have hv:=S.class_agrees S s.laws.toSymmetric (fun _=>le_rfl) (fun i=>(y i).1) hx (fun i=>(y i).2)
   have hu:=S.class_agrees S s.laws.toSymmetric (fun _=>le_rfl) (fun _:Fin 1=>e) (valid_one (0:Points 1)) (fun _=>a)
   have hv': S.useAt S x (S.classTokens ∘ y)=S.read x y:= hv
   have hu': S.useAt S (0 : Points 1) (S.classTokens ∘ fun _ => ⟨e,a⟩)=S.read (0:Points 1) (fun _ =>⟨e,a⟩):=hu
   change S.useAt S x _ = S.useAt S (0:Points 1) _
   rw [← hF,hv'];change _= S.useAt S (0:Points 1) (S.classTokens ∘ fun _ => ⟨e,a⟩)
   rw [hu']
   let swap:Equiv.Perm (Fin 2):=Equiv.swap 0 1
   let y' : Fin 2→C.book.Token:=Fin.cons (C.book.one d) (fun _:Fin 1=> ⟨e,a⟩)
   have hh:=s.laws.same swap hx y
   change S.read (Points.rearrange swap x) (y ∘ swap)= _ at hh
   rw [←hh, show y ∘ swap=y' from funext (Fin.cases (by simp [swap,y,y']) (fun i=>by fin_cases i; simp [Function.comp,y',y,swap]))]
   let x':=Points.rearrange swap x
   rw [show S.read (Points.rearrange swap x) y' = _ from s.laws.unital (d:=d) (Points.rearrange_in _ hx) (fun _:Fin 1=>⟨e,a⟩)] -- determine lemma
   change S.read x'.tail _ = S.read _ _
   rw [show x'.tail=Points.across (x 0) (0:Points 1) from PiLp.ext (fun i=>by fin_cases i; change x (swap 1)=0+x 0; simp [swap])]
   exact s.translations 1 (0:Points 1) (valid_one _) (x 0) _
lemma unit_left_read (s:S.Hierarchy){d e:ℕ}{v:S.Field d}(x:Points 2)(hx:x∈conf _): custom x (S.unit e) v=first_value d v:=by
   obtain ⟨a,ha⟩:=S.onto _ v
   rw [← ha]; unfold custom first_value
   let y: Fin 2→C.book.Token:= Fin.cons (C.book.one e) (fun _:Fin 1=>⟨d,a⟩)
   have hF : (S.classTokens ∘ y) = Fin.cons (α:=fun _:Fin 2=> S.Tag) ⟨e,S.unit e⟩ (fun _:Fin 1=> ⟨d,S.project _ a⟩):= funext (Fin.cases rfl (fun _=>rfl))
   have hv:=S.class_agrees S s.laws.toSymmetric (fun _=>le_rfl) (fun i=>(y i).1) hx (fun i=>(y i).2)
   have hu:=S.class_agrees S s.laws.toSymmetric (fun _=>le_rfl) (fun _:Fin 1=>d) (valid_one (0:Points 1)) (fun _=>a)
   have hv': S.useAt S x (S.classTokens ∘ y)=S.read x y:= hv
   have hu': S.useAt S (0 : Points 1) (S.classTokens ∘ fun _ => ⟨d,a⟩)=S.read (0:Points 1) (fun _ =>⟨d,a⟩):=hu
   change S.useAt S x _ = S.useAt S (0:Points 1) _
   rw [← hF,hv'];change _= S.useAt S (0:Points 1) (S.classTokens ∘ fun _ => ⟨d,a⟩)
   rw [hu']
   rw [show S.read x y = _ from s.laws.unital (d:=e) hx (fun _:Fin 1=>⟨d,a⟩)]
   rw [show x.tail=Points.across (x 1) (0:Points 1) from PiLp.ext (fun i=>by fin_cases i; change x 1=0+x 1; simp)]
   exact s.translations 1 (0:Points 1) (valid_one _) (x 1) _
lemma unit_mean (s:S.Hierarchy):first_value 4 (S.unit 4)=1:=(show first_value 4 (S.unit 4)=expectation S 4 (S.unit 4) by rw [expectation,Work.A01.front_eval];unfold first_value;congr 3;funext j; fin_cases j;rfl).trans (mean_unit (T:=S) s.laws)
lemma focus_read (s:S.Hierarchy){v:S.Field 4}(x:Points 2)(hx:x∈conf _): custom x (focus 4 v) (focus 4 v)= custom x v v - (first_value 4 v)^2:=by
   obtain ⟨L,hL⟩:=custom_linear (e:=4) x (focus 4 v)
   obtain ⟨M,hM⟩:=cu_linear₂ (v:=v) (d:=4) x
   obtain ⟨K,hK⟩:=cu_linear₂ (v:=S.unit 4) (d:=4) x
   rw [hL,focus,map_sub,map_smul];simp only [← hL,hM,hK,focus,map_sub,map_smul]; simp_rw [← hM,←hK,unit_left_read s x hx, unit_right_read s x hx, unit_mean s]; simp only [smul_eq_mul];ring
lemma derivative_focus (s:S.Hierarchy){d k:ℕ}{v:S.Field d}{w:S.Field k}{x:Points 2} (i : Axis)(hx:x∈conf _): customDer x i v (focus k w)=customDer x i v w:=by
   unfold customDer Points.gradient Analysis.D
   have hf : (fun y=>custom y v (focus k w)) =ᶠ[𝓝 x] (fun y=> custom y v w-first_value k w • first_value d v) := by
      filter_upwards [(conf_open _).eventually_mem hx] with y hy
      obtain ⟨L,hL⟩:=cu_linear₂ (v:=v) (d:=k) y
      rw [hL,focus,map_sub,map_smul,←hL]; simp only [←hL,unit_right_read s y hy]
   have hu: DifferentiableAt ℝ (fun y=>custom y v w) x:=((Ward.cont_disc s (Fin.cons ⟨d,v⟩ (fun _=>⟨k,w⟩)) hx).differentiableAt (by simp)) -- names
   rw [hf.fderiv_eq]
   rw [show (fun y:Points 2=> custom y v w-first_value k w • first_value d v) = (fun y=>custom y v w)-fun _=> (first_value k w • first_value d v) from rfl]
   rw [fderiv_sub hu (differentiableAt_const _), fderiv_const_apply];simp only [sub_zero]

-- Express scalar action at leading order on the actual unselected scaling curve;
-- the fields move, i.e. this does not say `traceField` has leading power.
variable (P:Scaling S)
local notation "s0" => scalarLabel C.labels

def scalarCompar : (Fin 2 → (E).Tag) := fun _ => ⟨4,s0⟩
def testScalar (i : ℕ) := P.U i 4 s0
lemma scalar_expression (x:Points 2) (i:ℕ) : Ward.disc (P.pins i ∘ (scalarCompar (C:=C))) x = custom x (testScalar P i) (testScalar P i):=by rw [custom_self];rfl
lemma free_expression (x:Points 2)(h:x∈conf _) : Ward.disc (scalarCompar (C:=C)) x = (↑((theoryDensity G)/‖x 0-x 1‖^8):ℂ):=by
   have hx: x 0≠x 1:=fun hh=> show False from (by decide : (0:Fin 2)≠1) (h hh)
   have hu : x=Maxwell.Free.pairPoints (x 0) (x 1):=PiLp.ext (fun j=>by fin_cases j <;> rfl)
   nth_rw 1 [hu]; change @Ward.disc _ _ (Bel C.book) _ (fun _=>⟨4,s0⟩) _ = ↑((theoryDensity G / ‖x 0-x 1‖^8):ℝ); have ht:= reference_pair C.labels hx
   exact ht.trans (by unfold theoryDensity; push_cast; ring)
lemma free_at_unit (s:ℝ)(hs:0<s):Ward.disc (scalarCompar (C:=C)) (separated s) = ↑(theoryDensity G/s^8):= by
   rw [free_expression (separated s) (by intro i j hij; by_contra hn;exact not_le_of_gt hs (one_mul (M:=ℝ) s ▸ ((room_separated _ hs.le).2 i j hn |>.trans (show _ ≤0 by rw [hij,sub_self,norm_zero]))))]
   change (↑(theoryDensity G/‖(0:E4)-s • basis timeAxis‖^8):ℂ)=_
   rw [zero_sub,norm_neg,norm_smul,basis_norm,Real.norm_of_nonneg hs.le,mul_one]
lemma unit_test (x:ℝ)(t:ℝ) : x • separated t=separated (x*t):=PiLp.ext (fun i=>by fin_cases i; exact smul_zero x; exact smul_smul x t _)
lemma compact_interval_window (M:ℝ) (hM:M>0) : ∃ R : ℝ,0<R ∧ ∀ x∈Icc (M⁻¹) M, separated x ∈Scaling.window R 2:=by
   let K:=separated '' Icc (M⁻¹) M
   have h: Continuous separated:= (PiLp.continuous_toLp _ _).comp (continuous_pi (fun i=> by fin_cases i <;> [exact continuous_const; exact continuous_id.smul continuous_const]))
   have hz : ∀ᶠ i in (atTop:Filter ℝ), K⊆Scaling.window i 2:=Work.A05.compact_fits (isCompact_Icc.image h) (by
       rintro y ⟨x,hx,rfl⟩ u v hy; by_contra h'; have ht:= room_separated x (hx.1.trans' (inv_nonneg.mpr hM.le)); exact not_le_of_gt ((inv_pos.mpr hM).trans_le hx.1) (one_mul (M:=ℝ) x ▸ (ht.2 u v h').trans (show _ ≤0 by rw [hy,sub_self,norm_zero])))
   obtain ⟨i,hi,he⟩:= (hz.and (eventually_gt_atTop 0)).exists
   exact ⟨i,he,fun x hx=> hi (mem_image_of_mem _ hx)⟩
local notation "density" => theoryDensity G
lemma test_interval (M:ℝ)(hM:M>0)(w:ℝ)(hw:0<w)
 (hf : ∀ R, 0<R→P.jets 2 4 0 R) : ∀ᶠ i in atTop,∀ x∈Icc M⁻¹ M,
 ‖custom (separated (P.r i*x)) (testScalar P i) (testScalar P i) - ↑(theoryDensity G/x^8)‖ ≤w:=by
   obtain ⟨R,hR,H⟩:= compact_interval_window M hM
   have ht:= hf R hR 2 le_rfl 0 le_rfl scalarCompar (fun _=>le_rfl) w hw
   filter_upwards [ht] with i hi x hx
   rw [←unit_test, ← scalar_expression,← free_at_unit _ ((inv_pos.mpr hM).trans_le hx.1)]
   rw [← norm_iteratedFDeriv_zero (𝕜:=ℝ) (f:=(fun y=>Ward.disc (P.pins i ∘ scalarCompar) (P.r i • y) -Ward.disc (scalarCompar (C:=C)) y)) (x:=separated x)]
   -- iteratedFDeriv_sub? need smoothness if order0 though ext
   calc _ = ‖iteratedFDeriv ℝ 0 (fun y=>Ward.disc (P.pins i ∘ scalarCompar) (P.r i • y)) _ -iteratedFDeriv ℝ 0 (Ward.disc (scalarCompar (C:=C))) _‖:= congr_arg (fun u=> ‖u‖) (ContinuousMultilinearMap.ext fun j=> by simp only [sub_apply,iteratedFDeriv_zero_apply])
        _ ≤ _:= hi _ (H _ hx)
lemma mean_scalar_free: first_value (S:=freeTable C.labels) 4 s0=0:=by
   unfold first_value; have he:=congr_arg (expectation (freeTable C.labels) 4) (scalar_actual C.labels); rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul, UVNext.FreeStress.total, map_sum] at he
   have hz (b): expectation _ 4 (∑ k:Axis, UVNext.FreeStress.flat C.labels b k b k)=0:=UVNext.FreeStress.panel_mean C.labels b b
   simp only [hz, Finset.sum_const_zero, smul_eq_mul] at he
   have h_eq : first_value (S:=freeTable C.labels) 4 s0= expectation (freeTable C.labels) 4 s0 := by rw [expectation,Work.A01.front_eval];unfold first_value;congr 3;funext j; fin_cases j;rfl
   change first_value (S:=freeTable C.labels) 4 s0=_; rw [h_eq]; exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)
lemma scalar_mean_leading (hf:∀ R,0<R→P.jets 1 4 0 R):Tendsto (fun i=>first_value 4 (testScalar P i)) atTop (𝓝 (first_value (S:=freeTable C.labels) 4 s0)):=by
    obtain ⟨R,hR,H⟩:= ((Work.A05.compact_fits (K:={(0:Points 1)}) isCompact_singleton (Set.singleton_subset_iff.mpr (valid_one _))).and (eventually_gt_atTop (0:ℝ))).exists
    rw [Metric.tendsto_nhds]; intro ε hε
    have ht:=hf R H 1 le_rfl 0 le_rfl (fun _:Fin 1=>(⟨4,s0⟩ : (E).Tag)) (fun _=>le_rfl) (ε/2) (by positivity)
    filter_upwards [ht] with i hi
    have hx:= hi _ (hR (Set.mem_singleton 0))
    rw [dist_eq_norm]
    apply lt_of_le_of_lt ?_ (half_lt_self hε)
    change ‖Ward.disc (P.pins i ∘ fun _:Fin 1=>(⟨4,s0⟩ : (E).Tag)) 0 - Ward.disc (fun _:Fin 1=>(⟨4,s0⟩ : (E).Tag)) 0‖ ≤ _
    calc _ = ‖iteratedFDeriv ℝ 0 (fun z=>Ward.disc (P.pins i ∘ fun _:Fin 1=>(⟨4,s0⟩ : (E).Tag)) (P.r i • z) - Ward.disc (fun _:Fin 1=>(⟨4,s0⟩ : (E).Tag)) z) 0‖ := by rw [norm_iteratedFDeriv_zero,smul_zero]
         _ = _ := congr_arg (fun u=> ‖u‖) (ContinuousMultilinearMap.ext fun j=> by simp only [sub_apply,iteratedFDeriv_zero_apply])
         _ ≤ _ := hx
lemma test_focus_interval (s:S.Hierarchy)(M:ℝ)(hM:M>0)(w:ℝ)(hw:0<w)
 (hf : ∀ R, 0<R→P.jets 2 4 0 R) : ∀ᶠ i in atTop,∀ x∈Icc M⁻¹ M,
 ‖custom (separated (P.r i*x)) (focus 4 (testScalar P i)) (focus _ (testScalar P i)) - ↑(theoryDensity G/x^8)‖ ≤w:=by
   have h:= test_interval P M hM (w/2) (by positivity) hf
   have ht:=scalar_mean_leading P (fun R hR=>fun _v hv=>hf R hR _ (hv.trans (show 1≤2 by omega))); rw [mean_scalar_free] at ht
   filter_upwards [h,(tendsto_order.mp (ht.norm.pow 2)).2 _ (show ‖(0:ℂ)‖^2 < w/2 from by rw [norm_zero,zero_pow (by decide : 2≠0)]; positivity)] with i hi hz x hx
   have hq:= mul_pos (P.positive i) ((inv_pos.mpr hM).trans_le hx.1)
   rw [focus_read s _ (show _ ∈conf _ from room_conf _ _ _ _ _ (room_separated _ hq.le) hq one_pos)] -- malformed; use room_conf
   let M:=testScalar P i
   let b:=custom (separated (P.r i*x)) M M; let z:= (↑(theoryDensity G/x^8):ℂ)
   change ‖b-_ - z‖ ≤ _
   have hh : ‖(first_value 4 (testScalar P i))^2‖ ≤ w/2:=by rw [norm_pow]; exact hz.le
   rw [sub_right_comm]; exact ((norm_sub_le ..).trans (add_le_add (hi x hx) hh)).trans_eq (add_halves _) 
local instance {k : ℕ} : ContinuousSMul ℝ (Points k) := IsBoundedSMul.continuousSMul
private lemma lined (x v : Points 2) : HasDerivAt (fun s:ℝ=>s • v+x) v (0:ℝ) :=by simpa only [id_eq,Pi.add_apply,one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const (𝕜':=ℝ) v).add_const x)
theorem free_rate : Points.gradient 0 timeAxis (Ward.disc (scalarCompar (C:=C))) (separated 1) = (↑(8*theoryDensity G):ℂ) := by
   let v:=Points.direction (n:=2) 0 timeAxis; let f:= Ward.disc (scalarCompar (C:=C))
   let x := separated 1
   have h(s:ℝ)(hs:s<1) : (s • v + x) 0-(s • v+x) 1=(s-1) • basis timeAxis := by
      change (s • v 0 + x 0)-(s • v 1 + x 1)=_
      rw [show v 0=basis timeAxis from by simp [v,Points.direction]] -- direction notation PiLp
      rw [show v 1=0 from ?_]; · change s • basis timeAxis + 0 - (_ + (1:ℝ) • basis _) = _; module
      simp [v,Points.direction]
   have he : (fun s:ℝ=> f (s • v+x)) =ᶠ[𝓝 0] (fun s=>Complex.ofReal (theoryDensity G / ((1-s)^8))) := by
       filter_upwards [eventually_lt_nhds (show (0:ℝ)<1 by norm_num)] with s hs
       have hW:=h s hs; have hne : (s • v+x).ofLp 0- (s • v+x).ofLp 1≠0:=hW.symm ▸ smul_ne_zero (by linarith) (by intro hx; have h:=congr_arg norm hx; simp at h)
       have hu : (s • v+x) ∈ conf _:=by
           intro i j hx; fin_cases i <;> fin_cases j <;> first | rfl | exact (sub_ne_zero.mp hne hx).elim | exact (sub_ne_zero.mp hne hx.symm).elim
       change Ward.disc (scalarCompar (C:=C)) (s • v+x)= _
       rw [free_expression _ hu,hW,norm_smul,basis_norm,mul_one,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr hs),neg_sub]
   have hd := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x:=0) ((hasDerivAt_const (0:ℝ) (theoryDensity G)).div (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id' 0)).pow 8) (by norm_num)))
   norm_num at hd
   have hD : DifferentiableAt ℝ f x := by
      have H' := Maxwell.Free.hierarchy C.book.grid
      exact (Ward.cont_disc H' (scalarCompar (C:=C)) (room_conf _ _ _ _ _ (room_separated 1 zero_le_one) one_pos one_pos)).differentiableAt (by simp)
   have hv: HasDerivAt (fun s:ℝ=> f (s • v+x)) (Points.gradient 0 timeAxis f x) 0:=by
       have hD' : DifferentiableAt ℝ f ((0:ℝ) • v+x) := by simpa using hD
       have hF := hD'.hasFDerivAt.comp_hasDerivAt (x:=(0:ℝ)) (f:=fun s=>(s:ℝ) • v+x) (lined x v) -- need point x defeq
       simpa only [Function.comp_def,Points.gradient, Analysis.D,zero_smul,zero_add,x,v] using hF
   apply hv.unique; convert hd.congr_of_eventuallyEq he using 1; push_cast; ring
lemma convergence_rate (s:S.Hierarchy)(hf:∀ R, 0<R→P.jets 2 4 1 R): Tendsto
    (fun k=> P.r k • customDer (separated (P.r k)) timeAxis (testScalar P k) (focus 4 (testScalar P k))) atTop (𝓝 (↑(8*theoryDensity G):ℂ)):=by
    let x:=separated 1; let v:=Points.direction (n:=2) 0 timeAxis
    let f(k:ℕ)(z:Points 2):=Ward.disc (P.pins k ∘ (fun _:Fin 2=>(⟨4,s0⟩ : (E).Tag))) (P.r k • z)
    have he: x∈conf 2:= room_conf _ _ _ _ _ (room_separated _ zero_le_one) one_pos one_pos
    obtain ⟨R,hR,H⟩:= ((Work.A05.compact_fits (K:={x}) isCompact_singleton (Set.singleton_subset_iff.mpr he)).and (eventually_gt_atTop (0:ℝ))).exists
    rw [Metric.tendsto_nhds]; intro ε hε
    have hv: 0 < ‖v‖+1:= add_pos_of_nonneg_of_pos (norm_nonneg _) (by norm_num)
    filter_upwards [hf R H 2 le_rfl 1 le_rfl (scalarCompar (C:=C)) (fun _=>le_rfl) ((ε/(‖v‖ +1))/2) (half_pos (div_pos hε hv))] with k hk; specialize hk _ (hR (Set.mem_singleton x))
    change ‖iteratedFDeriv ℝ 1 (f k) x - iteratedFDeriv ℝ 1 (Ward.disc (scalarCompar (C:=C))) x‖ ≤ _ at hk
    have h : P.r k • x∈conf _:=(Work.A05.smul_conf (P.positive k) he)
    have h' : P.r k •x=separated (P.r k):=(unit_test _ _).trans (congr_arg _ (mul_one _))
    calc _ = ‖(fderiv ℝ (f k) x) v - (fderiv ℝ (Ward.disc (scalarCompar (C:=C))) x) v‖:= by
             rw [derivative_focus s timeAxis (h' ▸ h), dist_eq_norm, ← free_rate, customDer, show (fun x=>custom x _ _)=_ from funext (fun x=> (scalar_expression P x k).symm)]
             rw [← h', ← Work.A04.gradient_scaled (P.r k) (Ward.disc (P.pins k ∘ scalarCompar)) x ?_ (0:Fin 2) timeAxis]
             · rfl
             exact ((Ward.cont_disc s (P.pins k ∘ _) h).differentiableAt (by simp))
         _ = ‖(iteratedFDeriv ℝ 1 (f k) x - iteratedFDeriv ℝ 1 (Ward.disc (scalarCompar (C:=C))) x) (fun _=>v)‖ :=by simp only [sub_apply,iteratedFDeriv_one_apply]
         _ ≤ ((ε/(‖v‖ +1))/2)*‖v‖ :=(ContinuousMultilinearMap.le_opNorm _ _).trans (by simpa using mul_le_mul_of_nonneg_right hk (norm_nonneg v))
         _ < ε := by have ht: 0<‖v‖+2 := add_pos_of_nonneg_of_pos (norm_nonneg _) (by norm_num); field_simp; nlinarith only [ht, hε]
end YM.Trace

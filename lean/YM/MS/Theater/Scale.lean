import YM.MS.Theater.Seat
/-!
# E4-frequency fields vs line momentum.Scalar real jets & complex evaluation.

 Phase matching Fourier derivative convention. Need dual shape image.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset MeasureTheory Real Maxwell
open Analysis Tensor Koszul Plane Landau Detect
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {J E K:Type}[Fintype J]{G:Gauge}{h i r n:ℕ}
   [NormedAddCommGroup E][NormedSpace ℝ E]
abbrev out : E4≃ₗ[ℝ] FourP:= WithLp.linearEquiv 2 ℝ _
abbrev fixF : FourP≃ₗ[ℝ] E4:= Theater.out.symm
abbrev RealP (E:Type)[NormedAddCommGroup E] [NormedSpace ℝ E] := E→ₗ[ℝ] ℂ
-- possible RealP on all.No norm on caller (uses LightC instances created via proper ambient). OK.
lemma read_1 (Q:PUnit)(_H:True) : Q=Q:= rfl -- remove
lemma lean_axis (p:FourP)(a:Axis): inner ℝ ( fixF p ) (basis a)=p a:= Eq.trans (real_inner_comm (basis a) _) ( basis_inner .. ) -- basis inferred? cf earlier
abbrev hitϑ (i:ℕ): ℂ:= Complex.I ^ i
lemma glow (i:ℕ): hitϑ i≠0:= pow_ne_zero _ Complex.I_ne_zero
lemma rig (L:RealP ( LightC J G h )): ∃ x y:LightC J G h,L=Complex.ofRealCLM.toLinearMap ∘ₗ ( ticket J G h x ) + I • ( Complex.ofRealCLM.toLinearMap ∘ₗ ( ticket J G h y ) ):= by
   obtain ⟨x,hx⟩:= seat_surj ( Complex.reCLM.toLinearMap ∘ₗ L ); obtain ⟨y,hy⟩:= seat_surj ( Complex.imCLM.toLinearMap ∘ₗ L ); refine ⟨ x,y,?_⟩; rw [hx,hy]; ext i; -- ext ℂ comps
   all_goals simp; rw [mul_comm]; exact (Complex.re_add_im _).symm
abbrev speak (h:ℕ)(t:J)(p:FourP)(v:G.Color):= planeC t h ( fixF p ) v
def item (t:J)(L:RealP ( LightC J G h ))(c:G.ColorIndex)(p:FourP): ℂ:= hitϑ h * L ( speak h t p (cl G c) )
lemma portθ (L:RealP ( LightC J G h ))(t:J)(c:G.ColorIndex): Shape ( item t L c ) (h:ℤ):= by
   have ht ( L:LightC J G h ) : ContDiff ℝ ∞ (fun p:FourP=> ( ticket J G h L ) ( speak h t p (cl G c) )):= by
       simp_rw [speak,excerpt]; exact ( contDiff_const.mul ( ( EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) c ).contDiff.comp ( ( diag_smooth (L.val t) ∞ ).comp ( fixF.toLinearMap.toContinuousLinearMap.contDiff ) ) ) ) -- ι binder
   have hv (L:LightC J G h)(v:ℝ)(p:FourP) : ticket J G h L ( speak h t (v • p) ( cl G c ))= v^h* ( ticket J G h L ( speak h t p ( cl G c ) ) ):= by unfold speak; rw [excerpt,excerpt, map_smul,homogeneous]; exact mul_left_comm ..
   obtain ⟨X,Y,rfl⟩:= rig L; let R(L:LightC J G h):= fun p:FourP=> ( ( ticket J G h L ( speak h t p (cl G c) ):ℝ ):ℂ );
   have hR(L:LightC J G h): Shape (R L) (h:ℤ):= by refine ⟨ Complex.ofRealCLM.contDiff.comp ( ht L ), fun i=>by omega,fun v p=>?_⟩; unfold R; rw [hv, zpow_natCast,Complex.real_smul]; push_cast; rfl
   exact Shape.scalar ( hitϑ _ ) (Shape.add (hR X) (Shape.scalar _ (hR Y)))
lemma select (L M:RealP ( LightC J G h ))(hp:∀ i,item i L=item i M): L=M:= by
    apply LinearMap.ext; intro u; suffices he:L-M=0 from sub_eq_zero.mp he ▸ rfl;
    have hr : Submodule.span ℝ {x:LightC J G h|∃ i:J,∃ k:G.ColorIndex,∃ p:E4,x=planeC i h p ( cl G k )} ≤ LinearMap.ker ( L-M ) := by
       rw [Submodule.span_le]; rintro x ⟨a,c,p,rfl⟩; refine (show ( L-M ) ( planeC a h p ( cl G c ) )=0 from ?x); apply sub_eq_zero.mpr; obtain ht:= congr_fun (congr_fun (hp a) c) ( Theater.out p ); unfold item speak at ht; rw [ LinearEquiv.symm_apply_apply ( out ) ] at ht; exact mul_left_cancel₀ ( glow _ ) ht
    rw [termsTop] at hr; exact LinearMap.ker_eq_top.mp ( top_le_iff.mp hr )
-- exhibit denominator-free inverse. Contract using tensors of f. Signature linear J.
variable (J) in
def load (f:J→ G.ColorIndex→ Tensor.T E4 ℂ h): RealP (LightC J G h) := {
   toFun X:= ∑ i:J, ∑ c:G.ColorIndex, ∑ j:Fin h→Axis, ( ( X.val i ) ( Fill j ) c :ℝ) • f i c ( Fill j )
   map_add' X Y:= by simp [add_smul, Finset.sum_add_distrib] -- smul real to ℂ.
   map_smul' b X:= by simp [ Finset.smul_sum,mul_smul] }
lemma load_at (f:J→ G.ColorIndex→ Tensor.T E4 ℂ h)(c:G.ColorIndex)(p:E4)(t:J): load J f (planeC t h p (cl G c))= amount h • diagonal (f t c) p:= by
   classical
   unfold load; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [ Finset.sum_eq_single_of_mem t (Finset.mem_univ t) ];
   · simp_rw [wearing]; rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c) ]; · rw [exprY, Finset.smul_sum ]; apply Finset.sum_congr rfl; intro i _; rw [ show (( amount h • ( (∏ k,inner ℝ p (Fill i k)) • cl G c )) c :ℝ)= amount h*(∏ k, p (i k)) from ?_,mul_smul ]; simp only [PiLp.smul_apply,smul_eq_mul,cl,EuclideanSpace.single_apply,↓reduceIte, mul_one]; simp_rw [show ∀ (i:Fin h→ Axis) (k:Fin h),inner ℝ p (Fill i k) = p (i k) from fun i k=> ( real_inner_comm ( Fill i k ) p ) |>.trans ( basis_inner .. )]; -- hp Bind
     intro i hi ht; simp [ cl,ht, ht.symm ]
   intro k hk hx; rw [ away h p _ hx ]; simp
lemma jetting (f:J→G.ColorIndex→FourP→ℂ)(h:ℕ)(H:∀ i j,Shape ( f i j ) (h:ℤ)): ∃ L:RealP ( LightC J G h ),∀ i,item i L=f i:= by
   let Z(i:J)(j:G.ColorIndex):= f i j ∘  out; -- unknown arg
   have hx i j : Shape ( Z i j ) (h:ℤ):= Shape.linear ( H i j ) ( out.toLinearMap.toContinuousLinearMap ); -- name
   let F(i:J)(j:G.ColorIndex):= coeff ( Z i j ) h 0; let L:= load J F; refine ⟨ ( hitϑ h )⁻¹ • ( amount h )⁻¹ • L,?_⟩;
   intro i; funext j p; change hitϑ h * (( hitϑ h )⁻¹ * (( amount h )⁻¹ • _))=_; rw [show L ( speak h i p (cl G j))=_ from load_at F j ( fixF p ) i, ←(hx i j).form ]; rw [inv_smul_smul₀ (amt_p h).ne',mul_inv_cancel_left₀ (glow h)]; rfl -- Equiv out
end YM.MS.Theater

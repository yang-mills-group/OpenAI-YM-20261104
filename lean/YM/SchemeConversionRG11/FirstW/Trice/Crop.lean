import YM.SchemeConversionRG11.FirstW.Trice.Bough
/-! Leading curvature at mark from Wilson bare second-order path calculus. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS
open scoped ContDiff BigOperators Classical Topology
variable {T:Itinerary}{G:Gauge}{S:Set E4} {A B:Sight T G}{p q:Axis→E4→ G.Color}{n:Side}
def bind (p:Axis→E4→G.Color)(s:Signed)(i:Axis)(v:E4):= violet s i • p (s.perm i) (Ortho.move s.ortho v)
lemma flare_p (s:Signed)(i:Axis): flareL ((posDir i).rotate s)=violet s i:= by cases h:s.flip i <;> simp [flareL,Step.rotate,violet,Push.FiniteDetection.Free.Hyper.flip,posDir,h]
lemma chosenR (h: landingL T S A p)(s:Signed): landingL T (Ortho.move s.ortho ⁻¹' S) (actC T s A) (bind p s):= by
 intro i; let t:Step:= (posDir i).rotate s
 rw [show stalkH T (actC T s A) i=circleR T s (peakC T A t) from funext fun j=>funext fun x=>by simp only [actC,stalkH,Bare.wideLink_apply,circleR,peakC,boardAt, LinearMap.smul_apply, LinearMap.proj_apply]; unfold t; split <;> simp_all]
 have hp (v:E4): boardAt (0:Cover) t (mapW p (Ortho.move s.ortho v))=bind p s i v:= by rw [board_spin]; unfold t;rw [flare_p]; rfl
 intro σ hs v hv y he; rw [← hp]; exact looksV h t σ hs _ hv (fun i=>s.act (y i)) (sold (T:= Rig.path T σ hs) s y he)
lemma pitched_skew (u v:Axis→E4→ G.Color)(x:E4)(a b:Axis): pitch u v a b x= -pitch u v b a x:= neg_sub ..|>.symm
lemma priced_pitch (p q:Axis→ E4→ G.Color)(s:Signed)(u v:Axis): pitch (bind p s) (bind q s) u v 0= (violet s u*violet s v) • pitch p q (s.perm u) (s.perm v) 0 := by
 simp only [pitch,bind,show s.ortho.move 0=0 from (Ortho.motion s.ortho).map_zero,map_smul,LinearMap.smul_apply,smul_sub,smul_smul]; rw [mul_comm (violet s v) (violet s u)]
lemma ClawAt0 (U V: FullT G n) (x:Site n): glint x 0 U V=(2:ℝ)⁻¹ • ((Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, Labels.Taylor.turn s.ortho (Bare.radialMap (door (fun i j=> spire G (affine s⁻¹ 0 x) (Lattice.square i j) (Bare.wideLink G s U) (Bare.wideLink G s V))))) := by
 have hp(U V: FullT G n)(x:Site n): (1/2:ℝ) • (rush G x 0 U V+ rush G x 0 V U)=door (fun i j=> spire G x (Lattice.square i j) U V):= by
    funext i j γ; have he (U V:FullT G n) : rush G x 0 U V i j γ = swerve x (Lattice.square i j) U V:= by
       simp only [rush, LinearMap.coe_mk,AddHom.coe_mk,LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]; rw [Finset.sum_eq_single_of_mem (∅: Finset (Fin 0)) (Finset.mem_univ _) (fun p _ e=>False.elim (e (Subsingleton.elim ..)))]; simp [Bare.walk, Bare.sign_eq,patch,Lattice.reverse]
    simp only [door,Pi.smul_apply,Pi.add_apply,he];rfl
 simp only [glint_once,sheer_eq,←hp,map_smul,map_add]; simp_rw [← Finset.smul_sum,Finset.sum_add_distrib,smul_add,smul_smul]; ring_nf
lemma opaline (h:landingL T S A p)(e:landingL T S B q)(hx:(0:E4)∈S) : Tendsto (fun k=>glint (0:Site (T.period k)) 0 (A k) (B k)) atTop (𝓝 ((2:ℝ)⁻¹ • Bare.radialMap (door (fun i j=>pitch p q i j 0)))) := by
 let X:= fun i j=> pitch p q i j 0
 let Y(s:Signed)(i j:Axis):= pitch (bind p s) (bind q s) i j 0
 let w(s:Signed)(k:ℕ): Bare.Response G 0:= door (fun i j=> claw T (actC T s A) (actC T s B) i j k 0)
 have hX(s:Signed): Tendsto (w s) atTop (𝓝 (door (Y s))) := by
    have hp : (0:E4)∈ Ortho.move s.ortho ⁻¹' S:= by change _ ∈ S; rw [show Ortho.move s.ortho 0=0 from (Ortho.motion _).map_zero]; exact hx
    exact tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> tendsto_pi_nhds.mpr fun _=>(clawV (chosenR h s) (chosenR e s) i j) id tendsto_id 0 hp 0 sails_zero
 let L(s:Signed):= Labels.Taylor.turn (G:=G) (j:=0) s.ortho ∘ₗ Bare.radialMap
 have he(s:Signed) : L s (door (Y s))=Bare.radialMap (door X):=by
   rw [show Y s=fun i j=> (violet s i * violet s j) • X (s.perm i) (s.perm j) from funext fun i=>funext fun j=> priced_pitch p q s i j]; exact radial_view X (pitched_skew p q _) _
 let F(s:Signed)(k:ℕ):= L s (w s k)
 have H:= tendsto_finsetSum (s:=Finset.univ) (fun s _=> show Tendsto (F s) atTop (𝓝 (Bare.radialMap (door X))) from he s ▸ (L s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hX s))
 let c:ℝ:= (Fintype.card Signed:ℝ)⁻¹; have ht:= H.const_smul c; rw [Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul ℝ,show ∀ v:Labels.Taylor G 0,c • ((Fintype.card Signed:ℝ) • v)=v from fun v=>inv_smul_smul₀ (by exact_mod_cast Fintype.card_ne_zero) _] at ht
 apply (ht.const_smul ((2:ℝ)⁻¹)).congr; intro i; rw [ClawAt0]; simp only [F,c,L,w,affine,Signed.act_zero,zero_add, actC, claw,LinearMap.comp_apply]
lemma stressF (b:Badge G)(z:Bool)(X Y U V:FullT G n)(t:ℝ)(u:Site n)(hx:0<t)(h:U=t • X)(e:V=t • Y): 2*lineReader z b.1 b.2 (glint u 0 X Y)= 2*(∑ i:Who G 6,token b z i * echoLeg t u i.val U V) := by rw [contact_l,h,e]; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]; field_simp [hx.ne']
def CardC (b:Badge G)(z:Bool)(t:ℝ)(u:Site n)(A B:FullT G n): ℝ:=2*(∑ i:Who G 6,token b z i * echoLeg t u i.val A B)
def FetchC (b:Badge G)(z:Bool)(u:Site n)(A B:FullT G n):ℝ:= 2*lineReader z b.1 b.2 (glint u 0 A B)
lemma packetC (b:Badge G)(z:Bool)(k:ℕ)(A B:Sight T G):FetchC b z (0:Site (T.period k)) (A k) (B k)= CardC b z (T.gap k) 0 (nativeM T A k) (nativeM T B k):= stressF _ _ _ _ _ _ (T.gap k) (0:Site (T.period k)) (T.positive _) rfl rfl
lemma receive (b:Badge G)(z:Bool)(h:landingL T S A p)(e:landingL T S B q)(hx:(0:E4)∈S): Tendsto (fun k=> CardC b z (T.gap k) 0 (nativeM T A k) (nativeM T B k)) atTop (𝓝 (lineReader z b.1 b.2 (Bare.radialMap (door (fun i j=>pitch p q i j 0))))) := by
 let F:=lineReader z b.1 b.2; have H:= (F.continuous_of_finiteDimensional.continuousAt.tendsto.comp (opaline h e hx)).const_mul (2:ℝ)
 rw [map_smul,smul_eq_mul, ←mul_assoc,mul_inv_cancel₀ (by norm_num),one_mul] at H; apply H.congr; intro i;  dsimp only [comp_apply,F]; rw [←packetC]; unfold FetchC; rfl
end YM.RG11.FirstW

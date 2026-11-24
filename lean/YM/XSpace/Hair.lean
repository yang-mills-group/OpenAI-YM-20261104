import YM.XSpace.Reason

/-!
# Constant color actions on the motif and pressure reads

Required for real physical counterterm construction: keep ALL `G.El`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Show
open Function Filter Set Lows Scale Mu Lattice Chart2 MvPolynomial Next.Rank.Normal Contraction Trace RG
open scoped Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{d:ℕ}(g:G.El)

def paint : Module.End ℝ (Contact G):= LinearMap.pi fun i=> G.adjoint g ∘ₗ LinearMap.proj i
lemma pigment (A:Contact G)(i:Edge Cover): paint g A i=G.adjoint g (A i):=rfl
lemma shade_price (p q:G.Color): inner ℝ (G.adjoint g p) (G.adjoint g q) =inner ℝ p q:= by
  let L: G.Color →ₗᵢ[ℝ] G.Color:=⟨G.adjoint g,G.norm_adjoint g⟩; exact L.inner_map_map ..
lemma tariff_inv (p:G.Color):G.adjoint g (G.adjoint g⁻¹ p)=p:=by rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]
lemma adj_state (p q:G.Color): G.adjoint g (G.ad p q)= G.ad (G.adjoint g p) (G.adjoint g q):=by
  apply G.colorMat_injective; simp only [G.mat_adjoint,G.colorMat_ad,Gauge.conjugate,mul_sub,sub_mul]; rw [mul_assoc]; congr! 1 <;> (simp [mul_assoc]; rw [← mul_assoc (star (G.mat g)), G.mat_star_mul,one_mul])

def mission (i: UnitIndex G): Line G:= ∑ j:G.ColorIndex,(G.adjoint g⁻¹ (basisC G i.2) j) • needle (i.1,j)
lemma sold (A:Contact G)(i:UnitIndex G): probe (mission g i) A = ram i (paint g A):=by
  rw [mission,map_sum, LinearMap.sum_apply]; change _ = (G.adjoint g (A i.1)) i.2;
  simp only [_root_.map_smul,LinearMap.smul_apply,probes,ram_at,smul_eq_mul]; rw [← EuclideanSpace.basisFun_inner _]; rw [show inner ℝ (basisC G i.2) (G.adjoint g (A i.1))=inner ℝ (G.adjoint g⁻¹ (basisC G i.2)) (A i.1) from ?_, PiLp.inner_apply]
  · simp [RCLike.inner_apply,mul_comm]
  rw [← shade_price g (G.adjoint g⁻¹ (basisC G i.2)), tariff_inv]
lemma bent (i:UnitIndex G): bake (mission g i)=paint g⁻¹ (bake (needle i)):=by
  unfold mission; simp only [_root_.map_sum, _root_.map_smul, baked]; funext j; rw [Finset.sum_apply,pigment]; dsimp only [Pi.smul_apply,φ]
  by_cases h:i.1.2=j.2; simp only [if_pos h, smul_comm _ (Sail.cover _), map_smul]; rw [← Finset.smul_sum]; exact congr_arg _ ((basisC G).sum_repr _)
  simp [h]
def castTone := exchange fun i=> complexCode G (mission g i)
set_option maxHeartbeats 300000 in
lemma greener (A:Contact G)(p:Stamp G):pit A (castTone g p)=pit (paint g A) p:=by
  suffices h:(pit A).comp (castTone g)=pit (paint g A) from DFunLike.congr_fun h p; ext1 i; rw [AlgHom.comp_apply,castTone,exchange_x]; change pit A (harp (mission g i))=_; rw [leg_test,sold]; symm; exact aeval_X _ _
lemma cast_wick (P:Stamp G): castTone g (flicker P)=flicker (castTone g P):=by
  unfold castTone flicker; rw [prepared, show scope (fun i=>complexCode G (mission g i)) (root G)= root G from ?_]
  apply Symmetric.ext; funext i j; change treats _ _ _=_; rw [heard,handshake, sold,bent g j,baked, ram_at,pigment,pigment, tariff_inv,← ram_at,Trace.rot, beaded]
lemma cast_frozen (p:Stamp G): castTone g (freeze p)=freeze (castTone g p):= no_twin (by rw [← cast_wick,gone,gone])
lemma cast_tie (p q:Stamp G): castTone g (tie G p q)=tie G (castTone g p) (castTone g q):=by rw [tie_ap,tie_ap,cast_wick,map_mul,cast_frozen,cast_frozen]
def Color (G:Gauge) (p:Stamp G):Prop := ∀ g:G.El, castTone g p=p
lemma tone {P:Stamp G}(h:∀ g:G.El,∀ A:Contact G,pit (paint g A) P=pit A P):Color G P:=fun g=> same (fun A=>by rw [greener,h])
lemma color_face (A:Contact G)(p:Face ℤ): linearFace p (paint g A)= G.adjoint g (linearFace p A) := by simp [angular,pigment]
lemma color_acc (A:Contact G)(p:Face ℤ): acc p (paint g A)=G.adjoint g (acc p A):=by
  rw [Outline.plays,Outline.plays,Outline.witness,Outline.witness,Finsupp.linearCombination_apply,Finsupp.linearCombination_apply,Finsupp.sum,Finsupp.sum,map_sum]; simp_rw [pigment,map_smul,adj_state]
lemma cast_V (p:Face ℤ): Color G (V3 G p):=tone fun g A=>by rw [price_at,price_at,diagnostic,diagnostic,color_face,color_acc,shade_price]

lemma color_trip (s:Lattice.Walk)(A:Contact G)(x:Cover): tallyPath x s (paint g A)=G.adjoint g (tallyPath x s A):=by induction s generalizing x with | nil=> simp [tallyPath] | cons i s ih=> simp_rw [tallyPath,LinearMap.add_apply,map_add,ih]; unfold Chart2.touch; rw [LinearMap.smul_apply,LinearMap.smul_apply,map_smul];rfl
lemma color_snd (A:Contact G)(s:RG.Slot): take2 s 0 (paint g A)=G.adjoint g (take2 s 0 A):=by
  simp only [take2,roundTrip,Drift.conjugate,native,face_c,face_a,map_zero,add_zero,trip_a,map_add, adj_state,color_face,color_acc,color_trip] -- good
open Wilson Source Source.Drops
variable {H:Hol G}(S:Survey G H d)
lemma color_prime (A:Contact G):primary S 0 (paint g A)=snapColor g (primary S 0 A):=by
  rw [primary_at,primary_at, show spectra S (0:Cover) (paint g A)=rotates g (spectra S 0 A) from funext fun i=>color_face g A _, S.extract_color]
lemma color_second (A:Contact G): secondary S 0 (paint g A)=snapColor g (secondary S 0 A):=by
  have hz := color_snd (G:=G) g A; let c:= LinearMap.toContinuousLinearMap (LinearMap.pi fun i:Fin S.size=> G.adjoint g ∘ₗ (LinearMap.proj (R:=ℝ) i))
  let a:=spectra S (0:Cover) A; have ht: spectra S (0:Cover) (paint g A)=c a:=funext fun i=> color_face g A _
  rw [secondary,secondary,map_add, show accent S (0:Cover) (paint g A)= rotates g (accent S 0 A) from funext fun i=> hz _,S.extract_color]; congr 1
  rw [ht]; let f:=S.recover; let L:=snapColor (G:=G) (d:=d) g; have he : f ∘ c=L ∘ f:=funext fun j=> S.recover_comm g j; unfold curvature2; rw [map_smul]; apply congr_arg (((2:ℝ)⁻¹) • ·)
  apply two_eq L f c S.recover_smooth he a
where two_eq {E F : Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (L:F→L[ℝ] F)(f:E→F) (c:E→L[ℝ] E) (h:ContDiff ℝ ω f)(he:f ∘ c=L ∘ f)(x:E):iteratedFDeriv ℝ 2 f 0 (fun _=> c x)= L (iteratedFDeriv ℝ 2 f 0 (fun _=> x)):=by
       have ht:= congr_arg (fun f:E→F=> iteratedFDeriv ℝ 2 f 0) he; rw [c.iteratedFDeriv_comp_right h _ le_top,L.iteratedFDeriv_comp_left h.contDiffAt le_top,map_zero] at ht; exact DFunLike.congr_fun ht (fun _=>x)
lemma powers (p:Labels.Label G d)(A:Snap G d):awaken d p.val (snapColor g A)=awaken d p.val A:= by rw [awaken,unfold_color]; exact p.property.2 ..
lemma program (p:Labels.Label G d):Color G (p0 S (0:Cover) p.val):=tone (fun g A=> by rw [awake0,awake0,color_prime,powers])
private lemma Proud.helper {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (L:E→L[ℝ] E)(f:E→ℂ)(h:f ∘ L=f)(hf:ContDiff ℝ ω f)(p q:E):fderiv ℝ f (L p) (L q)=fderiv ℝ f p q:=by
  have ht:= congr_arg (fun f:E→ℂ=> fderiv ℝ f p) h; rw [fderiv_comp p (hf.differentiable (by simp) _) L.differentiableAt,L.fderiv] at ht; exact DFunLike.congr_fun ht _
set_option maxHeartbeats 300000 in
private lemma proud_eq (p:Labels.Label G d) (A:Contact G) : pit (paint g A) (p1 S (0:Cover) p.val)=pit A (p1 S 0 p.val):=by
  let f:=awaken d p.val
  let B:=snapColor (G:=G) (d:=d) g
  have h:f ∘ B=f:=by funext x; dsimp only [f, B,Function.comp_apply]; rw [powers g p]
  have hh: ContDiff ℝ ω f:= by unfold f awaken; exact Work.G05.snap_read_smooth d p.val ω
  have he:= Proud.helper (E:=Snap G d) B f h hh (primary S (0: Cover) A) (secondary S (0: Cover) A)
  calc _ = _ := awake1 S (0:Cover) p.val (paint g A)
       _ = fderiv ℝ f (B (primary S (0:Cover) A)) (B (secondary S (0:Cover) A)) := by rw [color_prime g S A,color_second g S A]
       _ = _ := he.trans (awake1 S (0:Cover) p.val A).symm
lemma proud (p:Labels.Label G d):Color G (p1 S (0:Cover) p.val):=tone fun g A=> proud_eq g S p A

lemma plan (c:Shade.Cut)(a:ℝ)(p:On.Grade G d): Color G (Prelude.fuse S p c a):=by
  intro g; unfold Prelude.fuse Prelude.mark1; rw [map_sub,cast_tie, cast_wick]
  rw [show castTone g (p1 _ _ _ )=_ from proud S (Prelude.startField S p) g]
  unfold Prelude.enter0; rw [← Encore.tuned,show castTone g (p0 _ _ _)= _ from program S (Price.preparedL p) g]
  unfold Prelude.engine; set k:= Shade.outfit c a; simp_rw [_root_.map_sum,show ∀ f:Cover→Stamp G,castTone g ( Prelude.send k f)=Prelude.send k (fun i=>castTone g (f i)) from fun f=> Prelude.by_send (castTone g).toLinearMap k f, cast_V _ g]
end YM.XSpace.Show

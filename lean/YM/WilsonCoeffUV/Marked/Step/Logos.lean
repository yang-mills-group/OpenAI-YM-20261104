import YM.WilsonCoeffUV.Marked.Step.Conditional
/-!
# PDE extraction identity (address-Banach valued)

Used before estimates of *bulk*. Don't claim volume convergence at varying
markers/cutoffs from single-label formulas.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08
open scoped Topology BigOperators
variable {c f:Side}{ι U U':Type}{J I K S T:Finset ι}{D k:ι→ℕ}{i j e r h N m l:ℕ}{G:Gauge}{V:Type}[DecidableEq ι]

lemma cob_joy (h:J⊆ S)(X:Gen (Pen D J) U)(Y:Gen (Pen D (S\J)) U)(A:Case D): cloaks (touch A S).toLinearMap (cob h X Y)=fun i=> swirl (spore (cloaks (touch A J).toLinearMap X) (cloaks (touch A (S\J)).toLinearMap Y) i):=by
    funext r; change tinct (touch A S).toLinearMap (cob h X Y r)=_; rw [cob,cloak_swirl,map_sum,spore]; apply congr_arg swirl; apply Finset.sum_congr rfl; intro i hi; have ht:= Finset.mem_antidiagonal.mp hi; funext x; change touch A S (cobT _ _ _ _ _)=_; rw [cobT,dif_pos ht,waveJoy, joy_p, interweave,dif_pos ht]; rfl
omit [DecidableEq ι] in
lemma cloaked (A:Case D)(V:Matrix U U ℝ)[Fintype U](X:Layers ℝ U)(Y:Layers (Pen D S) U): cloaks (touch A S).toLinearMap (ravel V X Y i j)=ravel V X (fun i=>pPly A S (Y i)) i j:=by unfold ravel; simp_rw [map_sum,cloak_arbor]; rfl

section
variable [Fintype U]
def logos (V:Matrix U U ℝ)(h:J⊆ S)(X:Gen (Pen D J) U)(Y:Gen (Pen D (S\J)) U): Gen (Pen D S) U :=∑ i:U,∑ j:U,(V i j/2) • cob h (sever i X) (sever j Y)
def sewsV (V:Matrix U U ℝ)(h:J⊆ S)(X:Layers (Pen D J) U)(Y:Layers (Pen D (S\J)) U)(j e:ℕ): Gen (Pen D S) U :=∑ i∈Finset.antidiagonal j,∑ k∈Finset.antidiagonal e, logos V h (X i.1 k.1) (Y i.2 k.2)
lemma logosT (A: Case D)(V:Matrix U U ℝ)(h:J⊆ S)(X:Gen (Pen D J) U)(Y:Gen (Pen D (S\J)) U):
      cloaks (touch A S).toLinearMap (logos V h X Y)=arbor V (cloaks (touch A J).toLinearMap X) (cloaks (touch A (S\J)).toLinearMap Y):=by unfold logos arbor; simp_rw [map_sum,map_smul,cob_joy,cloak_sever]
lemma sewsMap (A: Case D)(V:Matrix U U ℝ)(h:J⊆ S)(X:Layers (Pen D J) U)(Y:Layers (Pen D (S\J)) U): cloaks (touch A S).toLinearMap (sewsV V h X Y i j)= ravel V (fun i=> pPly A J (X i)) (fun i=> pPly A (S\J) (Y i)) i j:=by unfold sewsV ravel; simp_rw [map_sum,logosT]; rfl

-- canonical coefficientwise log PDE readout
lemma touches (V:Matrix U U ℝ)(E:Layers ℝ U)(Z:thalamus D U)(h: ∀ S,Lit (mass k S) (Z S))(p:Lit 2 E)(l:∀ A:Case D,∀ S,let Y:=fun S=> skyVal A (Z S) (mass k S); let P:= ramp E 2
      brush none (Y S)= goLap V (Y S)+goLip V P (Y S)+goLip V.transpose P (Y S)+∑ J∈S.powerset,goLip V (Y J) (Y (S\J)))(i j:ℕ)(S:Finset ι):
    Z S (i+1) j=((i+1:ℕ):ℝ)⁻¹ • (ripple V (Z S i j)+ravel V E (Z S) i j+ravel V.transpose E (Z S) i j+∑ J∈S.powerset, if v:J⊆ S then sewsV V v (Z J) (Z (S\J)) i j else 0):=by
   let N A:=(((i+1:ℕ):ℝ))⁻¹ • (A:Gen (Pen D S) U)
   funext r x; apply pen_inj; intro A
   let t:= Z S; let X S i:= pPly A S (Z S i)
   have he S: stops (mass k S) (X S):=under_pen _ (h S).stop _; have hp S v i:Pure (X S v i):= ply_pure _ ((h S).shine_ v i)
   let C:= cloaks (U:=U) (touch A S).toLinearMap; let F:= ∑ J∈S.powerset, ravel V (X J) (X (S\J)) i j
   have hr: C (∑ J∈S.powerset, if v:J⊆ S then sewsV V v (Z J) (Z (S\J)) i j else 0)=F:=by
       rw [map_sum]; unfold F; apply Finset.sum_congr rfl; intro J h; rw [dif_pos (Finset.mem_powerset.mp h)]; exact sewsMap ..
   change X S (i+1) j r x= C (((i+1:ℕ):ℝ)⁻¹ • (ripple V (Z S i j)+ravel V E (Z S) i j+ravel V.transpose E (Z S) i j+∑ J∈S.powerset, if v:J⊆S then sewsV V v (Z J) (Z (S\J)) i j else 0)) r x; rw [map_smul,map_add,map_add,map_add,hr]; unfold C; rw [cloak_ripple,cloaked,cloaked]
   let D:= X S (i+1) j; let E':= X S i j; let d:= ramp E 2; let Y S:= skyVal A (Z S) (mass k S); let c:= ((i+1:ℕ):ℝ); have hx:=l A S
   change brush none (Y S)=goLap V (Y S)+goLip V d (Y S)+goLip V.transpose d (Y S)+∑ J∈S.powerset, goLip V (Y J) (Y (S\J)) at hx
   let L:= ripple V E'; let W v:= ravel v E (X S) i j; let T:= L+W V+W V.transpose+F
   have ht:FiniteGen L:= finite_ripple V (finite_stops (he S) i j); have hz v:FiniteGen (W v):=finite_ravel p.stop (he S) v; have hJ J:= finite_ravel (j:=i) (e:=j) (he J) (he (S\J)) V
   have hl:FiniteGen T := finite_add (finite_add (finite_add ht (hz _)) (hz _)) (finite_sum (fun i _=> hJ i))
   have hh: Pure T:=fun r=> (((pure_ripple V (hp S i j) r).add (pure_ravel V E (X S) i j r)).add (pure_ravel V.transpose _ _ _ _ _)).add (pure_sum (fun i _=>pure_ravel V (X i) (X (S\i)) _ _) r)
   have hd:= congr_arg (fun v:Ink (Option U)=>spanT i U (coeff j v)) hx; simp_rw [map_add,map_sum] at hd
   have hP v: spanT i U (coeff j (goLip v d (Y S)))=totalR (W v):=lip_count v E _ p.stop (he _) _ _ p.shine_ (hp _)
   have hc J : spanT i U (coeff j (goLip V (Y J) (Y (S\J)))) = totalR (ravel V (X J) (X (S\J)) i j):= lip_count V (X J) _ (he _) (he _) _ _ (hp _) (hp _)
   rw [dusk,glance (he S),lamp_count V _ (he _) i j (hp _ i j),hP,hP] at hd; simp_rw [hc] at hd
   have H: D=c⁻¹ • T:=by
       apply gen_inj (finite_stops (he S) (i+1) j) (finite_μ hl c⁻¹) (hp S (i+1) j) (fun i=> (hh i).smul c⁻¹)
       rw [visible_μ hl]
       have he': c • totalR D=totalR T:=by
           rw [Nat.cast_smul_eq_nsmul ℝ (i+1),hd]; unfold T; rw [visible_add (finite_add (finite_add ht (hz _)) (hz _)) (finite_sum (fun i _=>hJ i)),visible_add (finite_add ht (hz _)) (hz _),visible_add ht (hz _),visible_sum (fun i _=> hJ i)]
       rw [← he', smul_smul,inv_mul_cancel₀ (show c≠0 by unfold c; positivity),one_smul]
   exact congr_fun (congr_fun H r) x
end
end YM.WilsonCoeffUV.Wheel.Mark

import YM.OPE.Compatible.Fathom.Hollow
import YM.OPE.Compatible.Fathom.Cycle
/-!
# Tensor Schur identity
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d:ℕ}{K:KernelChoices}
open Silt.Float Silt Cloud
local notation "X!"=> Bid.Dir G n
lemma HatchM {I E:Type}[Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](L:E ≃L[ℝ] PAD I){A T:Mat I}(h:A.PosDef)(hp:A*T=1):∃ B:Law E,Silt.chamber B L.toContinuousLinearMap=T ∧∀ x y,B.P x y=(L x) ⬝ᵥ( A*ᵥL y):=by
      let V(x y:E):= L x ⬝ᵥ( A*ᵥ(L y)); have he(x):∃ q:Dual' E,V x=q:=⟨{toFun:=V x,map_add' a b:=by simp only[V,map_add,mulVec_add,dotProduct_add],map_smul' a b:=by simp only [V,map_smul,mulVec_smul,dotProduct_smul,RingHom.id_apply]},rfl⟩
      have hl:Aᵀ=A:= by rw[← conjTranspose_eq_transpose_of_trivial]; exact h.1.eq
      have hs(x y):V x y= V y x:=invertG _ _ hl -- scoping
      obtain ⟨P,hP⟩:=giraffe_addendum he hs; let B:=Libra.giraffe P (fun x y=>by rw[hP,hP]; exact hs ..) (fun x (hx:x≠0)=> by rw[hP]; have hx':L x≠0:=(by simpa using hx); simpa only [star_trivial] using h.dotProduct_mulVec_pos hx'); -- fix scoped names
      refine ⟨B,?_,hP⟩; have hC:= mul_eq_one_comm.mp hp; have ht:Tᵀ=T:=by rw [← Matrix.mul_one Tᵀ, ←hp, ← Matrix.mul_assoc,show Tᵀ*A=1 from by nth_rw 1[←hl];rw[← Matrix.transpose_mul,hp];simp, Matrix.one_mul]
      ext i j; let x' := T*ᵥ (Pi.single i 1); let v:=L.symm x'; have hb:L v=x':=L.apply_symm_apply _; have hh:coQ L i=P v:=by ext1 y; rw [hP,hs v y]; change L y i=L y ⬝ᵥ( A*ᵥ(L v)); rw [hb]; unfold x'; rw [mulVec_mulVec, hp,Matrix.one_mulVec, dotProduct_single_one]
      change coQ L j (B.inverse _)=_; rw [hh,show P v=B.P v from rfl,B.solves]; change L v j=_; rw[hb]; unfold x'; rw[mulVec_single_one]; exact congrFun (congrFun ht i) j -- x' equals Tᵀ i?
lemma Hport (C:KernelChoices)(v:Train r)(G:Gauge)(n:Side)(h:4 ≤ r):∃ B:Law (Bid.Dir G n), Silt.chamber B (flats G n).toContinuousLinearMap=CapeV C G v n∧∀ x y, B.P x y=flats G n x ⬝ᵥ( Shrink C G v n *ᵥ flats G n y ):=by refine HatchM (flats G n) (cloakElite C v G n h) ?_ ; convert! cloakR C v G n h using 1; congr; exact Subsingleton.elim ..
noncomputable abbrev Vessel (C:KernelChoices)(v:Train r)(G:Gauge)(n:Side)(h:4 ≤ r):= (Hport C v G n h).choose
noncomputable def rentV (G:Gauge)(v:Train r)(h:4≤r)(L:KernelChoices)(n:Side):RowB (Shade G) where
    val i j k:= (pointAt G v h L n).val i j k+if i=j then ((n.val:ℝ)^4)⁻¹ else 0
    fare:=(terra_money L h).choose+1
    positive:=by linarith only [(terra_money L h).choose_spec.1]
    lease i j k:=by
       apply (norm_add_le ..).trans; refine add_le_add ((pointAt G v h L n).lease ..) ?_; split; · rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by have h:1≤(n.val:ℝ):= Nat.one_le_cast.mpr n.pos; exact one_le_pow₀ h)
       simp only [norm_zero,zero_le_one]
lemma dripped (G:Gauge)(v:Train r)(h:4≤r)(L:KernelChoices)(a:Site n):Formed (rentV G v h L n).val ((CapeV L G v n).submatrix (station G n) (station G n)) a:=by
       intro b c i j; have ht:=(formsC (L:=L) v h a) b c i j; unfold CapeV rentV; rw [Matrix.submatrix_apply, Matrix.add_apply]; change Cot L G v n _ _ + tensor G (Resolvent.missing n) _ _=_; rw [ht]; apply congr_arg; change (if i.2=j.2 then Resolvent.missing n (a+wrap n _,coord i.1) (a+wrap n _,coord j.1) else 0)= _; rw [Resolvent.projected]; have hp: coord i.1=coord j.1 ↔ i.1=j.1:= axisEquiv.injective.eq_iff
       by_cases he:i.2=j.2 <;> by_cases hq:i.1=j.1<;>simp [he,hq,hp,Prod.ext_iff]; -- possible simp_loops
lemma wave {I:Type}{F:Filter I}(u:I→Side)(hp:Tendsto (fun i=>(u i).val) F atTop)(G:Gauge)(v:Train r)(h:4≤r)(L:KernelChoices): Dull F (fun i=>rentV G v h L (u i)) (atlasF G v h L):=by
       let t:= terra_money L h; refine ⟨⟨_,show 0≤t.choose+1 from add_nonneg (t.choose_spec.1) zero_le_one,Eventually.of_forall fun _=> le_rfl⟩, fun a b x=>?_⟩; let f(i:I):=((u i).val:ℝ); have ht:Tendsto f F atTop:=tendsto_natCast_atTop_atTop.comp hp
       have he:= (farN _ u v h L hp).2 a b x
       have hh: Tendsto (fun i:I=> if a=b then (f i^4)⁻¹ else 0) F (𝓝 0):=by
            by_cases h:a=b
            · subst b; simp only [if_true]; exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α:=ℝ) (by decide : 4≠0)).comp ht)
            simp only [if_neg h]; exact tendsto_const_nhds
       convert! he.add hh using 1; simp
end YM.OPE.Cascade.Paver

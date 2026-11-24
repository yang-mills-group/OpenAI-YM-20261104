import YM.OPE.Compatible.Ash.Reed
import YM.Lattice.Subdivision
/-! # Geometric sampling maps -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {n m:Side}
abbrev sizeR (n:Side):ℝ:= n.val
lemma embed_ret (r:Ratio n m)(p:Site n): moment (r.embed p)=moment p:=by
   ext i; simp only [moment_apply,r.lift_embed, Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]
   unfold mesh; rw [r.exact_size, Nat.cast_mul]; field_simp
lemma embed_sig (r:Ratio n m)(p: Site n)(a: Cover): char (r.embed p) (wrap m a)=char p (wrap n a):=by rw [char_wrapped, char_wrapped, embed_ret]
def smaller (_r:Ratio n m)(p:Site n):= wrap m (Lattice.lift p)
lemma lift_smaller (r:Ratio n m)(p:Site n): Lattice.lift (smaller r p)=Lattice.lift p:=by
   rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩
   have hs: n.val ≤ m.val:=r.exact_size ▸ Nat.le_mul_of_pos_right n.val r.count.property; have hv:=lift_centers p i; exact ⟨lt_of_le_of_lt (neg_le_neg (by exact_mod_cast hs)) hv.1, le_trans hv.2 (by exact_mod_cast hs)⟩
lemma nearer (r:Ratio n m):Injective (smaller r):=by
   intro x y hxy; have hx:Lattice.lift x=Lattice.lift y:=by rw [←lift_smaller r x, ←lift_smaller r y,hxy]
   calc x=wrap n (Lattice.lift x):=(wrap_lift _).symm
        _=y :=by rw [hx, wrap_lift]
def dew (n:Side):= (sizeR n)⁻¹
lemma dew_pos (n:Side) : 0<dew n:= inv_pos.mpr (by unfold sizeR; positivity)
lemma stretch_same (r:Ratio n m)(p:Site n)(s:ℝ)(hs:0<s): stretch (dew m*s) (smaller r p)=stretch (dew n*s) p:=by
   ext i; simp only [stretch, PiLp.smul_apply, smul_eq_mul, moment_apply, lift_smaller]; unfold mesh dew sizeR; field_simp
lemma smaller_sig (r:Ratio n m)(p z:Site n): char (smaller r p) (r.embed z)=char p z:=by
   rw [Pert.Full.swap, smaller,embed_sig,wrap_lift,Pert.Full.swap]
lemma bigger_far (r:Ratio n m)(p:Site m)(he:p∉ range (smaller r))(s:ℝ)(hs:0<s)(hv:dew n*s ≤ 1):2 ≤ ‖stretch (dew m*s) p‖:=by
   let a:=Lattice.lift p; let x:=wrap n a; have hh:a≠Lattice.lift x:=fun hh=>he ⟨x,(by unfold smaller; rw [←hh]; exact wrap_lift _)⟩
   rw [stretch_norm (mul_pos (dew_pos _) hs),le_div_iff₀ (mul_pos (dew_pos _) hs)]; have hb: incVec (mesh n) a=(sizeR m*dew n) • moment p:=by rw [moment,to_grid]; congr 1; unfold sizeR dew mesh; dsimp only[sizeR]; field_simp
   have hx:= Pert.Band.spill (n:=n) (v:=0) (j:=0) (f:=0) a hh; rw [hb,norm_smul,Real.norm_of_nonneg (by exact (mul_pos (val_pos m) (dew_pos n)).le)] at hx
   apply le_of_mul_le_mul_left (a:=sizeR m*dew n) ?_ (mul_pos (val_pos _) (dew_pos _)); apply le_trans _ (le_trans (b:=Real.pi) (le_of_lt Real.pi_gt_three) hx); rw [show sizeR m*dew n*(2*(dew m*s))= 2*(dew n*s) from by unfold dew; field_simp]; linarith only [hv]
structure Gloam where
   M:ℕ→Side
   q:Side
   growth:q.val>1
   law:∀ i, (M (i+1)).val=(M i).val*q.val
namespace Gloam
variable (U:Gloam)
def nb (i:ℕ):ℝ:=sizeR (U.M i)
def q' :ℝ :=sizeR U.q
def h(i:ℕ):ℝ:=dew (U.M i)
lemma qsub : 1< U.q':= by unfold q' sizeR; exact_mod_cast U.growth
lemma n_succ (i:ℕ): U.nb (i+1)=U.nb i*U.q':=by unfold nb q' sizeR; rw [U.law]; exact Nat.cast_mul ..
lemma n_eq (i:ℕ): U.nb i=U.nb 0*U.q'^i:=by induction i with |zero=>simp |succ i ih=>rw [n_succ,ih,pow_succ];ring
lemma h_succ(i:ℕ): U.h (i+1)=U.h i/U.q':=by change (U.nb _)⁻¹=(U.nb _)⁻¹ /_; rw [U.n_succ,mul_inv,div_eq_mul_inv]
lemma h_pos(i:ℕ):0<U.h i:=dew_pos _
lemma geom : Tendsto U.nb atTop atTop:=by
   rw [show U.nb=(fun i=>U.nb 0*U.q'^i) from funext fun i=>U.n_eq i]
   -- rw changed RHS goal both? nb circul
   exact Tendsto.const_mul_atTop (val_pos (U.M 0)) (tendsto_pow_atTop_atTop_of_one_lt U.qsub)
lemma h_null:Tendsto U.h atTop (𝓝 0):= tendsto_inv_atTop_zero.comp U.geom
lemma sides: Tendsto (fun i=>(U.M i).val) atTop atTop:=by
    rw [Filter.tendsto_atTop]; intro b; apply (U.geom.eventually (eventually_ge_atTop (b:ℝ))).mono
    intro i hi; change (b:ℝ)≤ (U.M i).val at hi; exact_mod_cast hi
def ratio(i:ℕ):Ratio (U.M i) (U.M (i+1)):=⟨U.q,U.law i⟩
lemma mesh_h(i:ℕ):mesh (U.M i)=turn*U.h i:=by rw [h,mesh,div_eq_mul_inv]; rfl
end Gloam
end YM.OPE.Balsam

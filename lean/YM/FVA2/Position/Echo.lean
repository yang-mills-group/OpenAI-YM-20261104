import YM.MS.Halo.Air
import YM.MS.Motif.Pulp
import YM.MS.Theater.Well

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset
open MS MS.Plane MS.Koszul MS.Motif MS.Arts MS.Halo
open MS.Landau MS.Book
open Analysis Tensor Maxwell Labels MS.Theater
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {G:Gauge} {m n h:ℕ} {x:E4} {z:ℂ} {a b c:Axis}
/-- `(x⋅∇)^n` on chosen curvature. No summing continued dimensions or evaluation
by four-dimensional EOM. Uses exactly the free color index convention by Lie basis.
-/
def graft (z:ℂ)(a b:Axis)(x:E4): ℕ→ Mield G m
 | 0=> cur z (chair m a) (chair m b)
 | k+1=> ∑ j:Axis,(x j) • convoke z (chair m j) (graft z a b x k)
lemma graft_add (z:ℂ)(a b:Axis)(x:E4)(k:ℕ): graft (G:=G) (m:=m) z a b x (k+1) = ∑ j:Axis, (x j) • convoke z (chair m j) (graft z a b x k):= rfl
lemma graft_alt : graft z a b x h= -graft (G:=G) (m:=m) z b a x h:= by
 induction h with
 | zero=> unfold graft cur; rw [jaw_skew (realA (G:=G) (chair m a)).tune (realA (G:=G) (chair m b)).tune]; simp only [cross_false,neg_one_smul, smul_neg, F₀]; abel
 | succ k ih=> unfold graft; rw [ih]; simp
abbrev slotDen (n:ℕ):ℝ:= (n+2)*(Nat.factorial n:ℝ)
abbrev Ray (G:Gauge)(m n:ℕ)(z:ℂ)(a:Axis) (x:E4): Mield G m:= (slotDen n)⁻¹ • ∑ i:Axis,x i • graft z i a x n
lemma title (x:E4): ∑ i:Axis,x i • Ray G m n z i x=0:= by
  unfold Ray; simp_rw [smul_comm (x _) (slotDen _)⁻¹, ← Finset.smul_sum]; apply smul_eq_zero.mpr; right
  simp_rw [Finset.smul_sum]; apply neg_eq_self.mp
  nth_rw 1 [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=>?_ )); conv_lhs=> rw [graft_alt]; rw [smul_neg, smul_neg, neg_neg]; exact smul_comm ..
private lemma pattern (k:ℕ) (F: Mield G m→ₗ[ℝ] G.Color) : ∃ T: Tensor.T E4 G.Color k, Tensor.diagonal T= fun x=> F (graft z a b x k):= by
 induction k generalizing F with
 | zero => exact ⟨ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _:Fin 0 => E4) (F (cur z (chair m a) (chair m b))),rfl ⟩
 | succ k ih=> choose t ht using fun j=> ih ( F.comp ((convoke (G:=G) z (chair m j )).restrictScalars ℝ)); refine ⟨ ∑ i:Axis, added (t i) (compAxis i), ?_⟩; funext x; unfold Tensor.diagonal; simp_rw [ _root_.sum_apply,graft_add,map_sum,map_smul]; exact Finset.sum_congr rfl (fun i _=> (added_diag (t i) (compAxis i) x).trans (by rw [ ht ] ; rfl))
def Generates (v:Labels.Taylor G h)(z:ℂ) (F:Mield G m→ₗ[ℝ] G.Color): Prop:= ∀ i x, v.value i x= F (Ray G m h z i x)
lemma produced (F:Mield G m→ₗ[ℝ] G.Color) (z:ℂ): ∃ x:Labels.Taylor G h, Generates x z F:= by
 choose f hf using fun (a b:Axis)=> pattern (z:=z) (a:=a) (b:=b) h F
 let T(a:Axis): Tensor.T E4 G.Color (h+1):= Tensor.symmetrize ((slotDen h)⁻¹ • ∑ i:Axis, added (f i a) (compAxis i))
 have he (a x): Tensor.diagonal (T a) x = F (Ray G m h z a x):= by
      unfold T Ray; rw [Tensor.symmetrize_diagonal,map_smul,map_sum]; change (slotDen h)⁻¹ • ((∑ i:Axis, added (f i a) (compAxis i)) (fun _=> x))=_; congr 1; simp_rw [map_smul]; rw [_root_.sum_apply]; exact Finset.sum_congr rfl (fun i _=> (added_diag (f i a) (compAxis i) x).trans (by rw [hf]; rfl))
 refine ⟨⟨T,(fun _=> Tensor.symmetrize_sym _), fun z=>?_⟩,he⟩
 simp only [he,← map_smul,← map_sum]; rw [title,map_zero]
private abbrev splitM (u: Legs (Shore G m)) (f:ℂ→ₗ[ℝ] ℝ): Mield G m→ₗ[ℝ] G.Color where
   toFun X:= WithLp.toLp 2 (fun i=> f ( X i u ))
   map_add' X Y:= by ext i; exact map_add f (X i u) (Y i u)
   map_smul' c X:= by ext i; exact map_smul f c (X i u)
private abbrev sprout {m:ℕ} (k:ℕ) (u:Legs (Shore G m))(z:ℂ)(f:ℂ→ₗ[ℝ] ℝ): Labels.Taylor G k:= (produced (m:=m) (h:=k) (splitM u f) z).choose
local notation "ρ" => Complex.reCLM.toLinearMap
local notation "μ" => Complex.imCLM.toLinearMap
def Ramp (G:Gauge)(h:ℕ) : Witness G h→ₗ[ℂ] ( ℂ→ Mob G ) where
   toFun X z m u:= X (sprout h u z ρ)+I*X (sprout h u z μ)
   map_add' X Y:= by funext z m u; change _= (X _+I*X _)+( Y _+I*Y _ ); rw [LinearMap.add_apply,LinearMap.add_apply,mul_add]; abel
   map_smul' c X:= by funext z m u; change c*X _ + _= c*(_+_); change _+ I*( c*X _)=_; ring
abbrev Coord (G:Gauge)(k:ℕ):= Module.Dual ℝ (Labels.Taylor G k)
abbrev asC (G: Gauge) (k:ℕ): Coord G k→ₗ[ℝ] Witness G k where
   toFun L:= Complex.ofRealCLM.toLinearMap.comp L
   map_add' := by intros; ext; exact Complex.ofReal_add ..
   map_smul' := by intros; ext; exact map_smul Complex.ofRealCLM ..
def Prong (a:Axis)(x:E4)(c:G.ColorIndex): Coord G h where
 toFun X:= X.value a x c
 map_add' := fun _ _=> rfl
 map_smul':= fun _ _=> rfl
theorem ramp_Jrad (c:G.ColorIndex): Ramp G h (asC G h (Prong a x c)) z m= Ray G m h z a x c:= by
 funext u; change (↑((sprout h u z ρ).value a x c):ℂ)+I*(↑( (sprout h u z μ).value a x c ):ℂ)= (Ray G _ _ _ _ _ c) u
 rw [show (sprout h u z ρ).value a x = _ from (produced (h:=h) (m:=m) (G:=G) (splitM u _) z).choose_spec a x]; -- unification ??
 rw [show (sprout h u z μ).value a x = _ from (produced (h:=h) (m:=m) (G:=G) (splitM u _) z).choose_spec a x]; rw [mul_comm]; exact Complex.re_add_im _
def Samples (G:Gauge)(h:ℕ):= { f:Coord G h|∃ a x c, f=Prong a x c }
lemma many (G:Gauge)(h:ℕ): Submodule.span ℝ (Samples G h)=⊤:= by
 let X:= Submodule.span ℝ (Samples G h)
 change X=_; suffices he:X.dualCoannihilator=⊥ by rw [ ← Subspace.dualCoannihilator_dualAnnihilator_eq ( W:=X ), he, Submodule.dualAnnihilator_bot]
 apply eq_bot_iff.mpr; intro L hL; apply (Submodule.mem_bot _).mpr; apply Labels.Taylor.value_ext
 funext a x; ext c; exact (Submodule.mem_dualCoannihilator _).mp hL (Prong a x c) ( Submodule.subset_span (show Prong a x c∈ Samples G h from ⟨a,x,c,rfl⟩) )
end YM.FVA2.Position.OpenAxis

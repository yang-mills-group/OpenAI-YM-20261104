import YM.WilsonCoeffUV.Product.Report.Center
/-!
# Pointwise smooth profiles in physical coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
abbrev Phrase (i):= Embroider.Scroll i
abbrev CellR:= Embroider.Chamber
abbrev Point4:= Embroider.E
def actualW (x:Cover):Point4:= fun i=> (x i:ℤ)
lemma actual_plus (x y:Cover) : actualW (x+y)=actualW x+actualW y :=by ext; simp [actualW]
lemma actual_minus (x y:Cover): actualW (x-y)=actualW x-actualW y:=by ext; simp [actualW]
lemma actual_mult (n:ℕ)(x:Cover): actualW (n•x)=(n:ℝ) • actualW x:=by ext; simp [actualW]
-- pull profile: tiled test center, λ m physical native. **test profile in physical coordinates**.
def position (rho L:ℝ)(o:CellR)(x:Cover): Point4:= rho • actualW x-L • o.val
def address (rho L:ℝ)(o:CellR)(x:Cover)(v:Point4): Point4:= position rho L o x+rho • v
lemma address_cont (rho L:ℝ)(x:Cover): Continuous (fun p:CellR×CellR=> address rho L p.1 x p.2.val):=by unfold address position; fun_prop
def sonal (rho L:ℝ)(o: CellR)(x:Cover)(φ:Phrase D): Phrase D := ⟨φ.val ∘ address rho L o x, by change ContDiff ℝ (↑D) _; apply (scribble φ le_rfl).comp; unfold address; fun_prop⟩
lemma currentP (rho L:ℝ)(o: CellR)(x:Cover)(φ:Phrase D)(v:Fin r→Axis)(p:r≤ D)(w:Point4): crease (sonal rho L o x φ) v w= rho^r*crease φ v (address rho L o x w):=by
    let a:=position rho L o x; let g (y:E):= φ.val (a+y); let t:E→L[ℝ] E:= rho • ContinuousLinearMap.id ℝ E
    have he : ContDiff ℝ (↑D) g:= (scribble φ le_rfl).comp (contDiff_const.add contDiff_id)
    change iteratedFDeriv ℝ r (g ∘ t) w _=_
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ he _ (Nat.cast_le.mpr p),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ r g _ (fun i:Fin r=> rho • ((Embroider.dot ∘ v) i))= _
    rw [(iteratedFDeriv ℝ r g _).map_smul_univ (fun _ => rho) (Embroider.dot ∘ v),show iteratedFDeriv ℝ r g (t w)= _ from iteratedFDeriv_comp_add_left r a _]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin, smul_eq_mul]; rfl
lemma roofA (P:Patch)(t v:ℝ)(p:CellR)(x:Cover)(w:Site P.L)(u:E): address (t*P.L.val) v p x (tucks P w u)=address t v p (P.L.val • x+lift w) u:=by
    unfold address position tucks offset; rw [actual_plus,actual_mult]; ext; simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul,actualW, speck]; field_simp; ring
lemma growingP (P:Patch)(t v:ℝ)(p:CellR)(x:Cover)(w:Site P.L)(φ:Phrase D): growWord P w D (sonal (t*P.L.val) v p x φ) = sonal t v p (P.L.val • x+lift w) φ:= Subtype.ext (funext fun i=> congr_arg φ.val (roofA P t v p x w i))
-- Cell interpolation exact and continuous; lens page cost measured sup.
abbrev Lounge:= ContinuousMap CellR ℝ
def wheelC (rho L:ℝ)(x:Cover)(φ:Phrase D): ContinuousMap CellR (Embroider.Volume D) := ⟨fun c=> page D (sonal rho L c x φ),by
    refine Continuous.subtype_mk ?_ _;
    apply continuous_pi; intro i;
    let T:ContinuousMap (CellR×CellR) ℝ:= ⟨fun a=> rho^i.1.val * crease φ i.2 (address rho L a.1 x a.2.val), continuous_const.mul ((continuous_iff_continuousAt.mpr (fun a=>Analysis.iterD (x:=a) (scribble φ (Nat.le_of_lt_succ i.1.isLt)).contDiffAt (Embroider.dot ∘ i.2))).comp (address_cont rho L x))⟩
    refine T.curry.continuous.congr (fun y=> ?_); ext v; exact (currentP rho L y x φ i.2 (Nat.le_of_lt_succ i.1.isLt) v.val).symm⟩
def nestC (c:CellR): Lounge→ₐ[ℝ]ℝ := ContinuousMap.evalAlgHom ℝ ℝ c
def century (c:CellR): Lounge→L[ℝ]ℝ:= ContinuousMap.evalCLM ℝ c
lemma nest_v (c:CellR)(V:Lounge): nestC c V=century c V:=rfl
noncomputable def demonstrate (X:ContinuousMap CellR (Volume D)): Vote D→L[ℝ] Lounge:=
    let f: Vote D →ₗ[ℝ] Lounge:={ toFun v:= ⟨fun i=> v (X i),v.continuous.comp X.continuous⟩, map_add' _ _:=by ext; rfl, map_smul' _ _:=by ext; rfl }
    f.mkContinuous ‖X‖ (fun i=> by rw [mul_comm]; exact (ContinuousMap.norm_le _ (by positivity)).mpr (fun w=> (i.le_opNorm (X w)).trans (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm ..) (norm_nonneg _))))
lemma demonstrate_at (X:ContinuousMap CellR (Volume D))(b:Vote D)(c:CellR): demonstrate X b c=b (X c):=rfl
end YM.WilsonCoeffUV.Mer

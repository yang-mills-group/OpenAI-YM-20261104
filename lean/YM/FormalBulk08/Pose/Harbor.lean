import YM.FormalBulk08.Pose.Wise

/-! Finite linear lens (complex SectionData). `Pol` used *before quotient*.
Read radial coefficient l then archive at
weight m+|ν|; make unobservable extension choices only for norm
operations (of noninvariant arrays). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Pose
open Filter Function Lattice Laurent Gauge Wilson Exterior Stationary
open Lava Lotus Mesa Gorge Shore City Kemp Rift
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius ComplexConjugate Classical
variable {G : Gauge} {r u d j n D m:ℕ} {η A θ B : ℝ} {I : Type*}
variable (F: Labels.Frame G d)

lemma place_sur (G:Gauge)(d:ℕ) : ∃ q: Pol G →ₗ[ℂ] Label G d, ∀ x:Label G d,q x.val=x := by
   obtain ⟨p,hp⟩:= (localFields G d).exists_isCompl
   exact ⟨(localFields G d).projectionOnto p hp,fun x=>Submodule.projectionOnto_apply_left hp x⟩
def pieceL (G:Gauge)(d:ℕ) : Pol G→ₗ[ℂ]Label G d:= (place_sur G d).choose
lemma pieceL_apply (G:Gauge)(d:ℕ)(x:Label G d): pieceL G d x.val=x := (place_sur G d).choose_spec x

def tide (M:Slate G d n): Tensor.T (Snap G d) ℂ n:= Complex.ofRealCLM.compContinuousMultilinearMap M
lemma tide_at (M:Slate G d n)(x): tide M x=((M x:ℝ):ℂ):=rfl
lemma tide_symm {M:Slate G d n}(h:Tensor.Sym M): Tensor.Sym (tide M):= by intro v s; rw [tide_at,tide_at,h]

-- Color expenditure suffices derive grade membership via Card operations;
-- all marks include it (separate mark transforms).
def lent (M:Slate G d n)(m:ℕ):Label G d:= pieceL G d (WardBin.tile (tide M) m)
def pocket (M:Slate G d n)(m:ℕ) : F.Coeff:= F.coords (lent M m)
lemma pocket_at (M:Slate G d n)(i:F.Index)(m): pocket F M m i=F.coords (pieceL G d (WardBin.tile (tide M) m)) i:=rfl
def Monic (M:Slate G d n):= Tensor.Sym M ∧ ∀ g x,M (colorIn G d g ∘ x)=M x
lemma monic_slate (p:Loc G 1)(T:Tile (edgeL G) r)(H:Hol G)(hs:0<η)(ht: Knoxville (fame _) η (0,p) T A)(hy:Lust T) (m n): Monic (slate T m n):= ⟨slate_symm p T m n hs ht, color_slate H p T hy hs ht⟩ -- arity functions explicit
lemma coast_pres {M: Slate G d n}(h:Monic M): Parts.Safe (Tensor.diagonal (tide M)):= by
    let K:=tide M; refine ⟨(Tensor.diag_smooth _ _).contDiffAt, fun u=>.of_forall fun x=>?_⟩
    change K (fun _=>_) = K (fun _=>x); unfold K; rw [tide_at,tide_at]; exact congr_arg _ (h.2 u _)
-- helper general
lemma slate_leads {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{M : Tensor.T E ℂ n}(hs:Tensor.Sym M): Tensor.coeff (Tensor.diagonal M) n 0=M:= by
   apply Tensor.ext_diag _ _ (Tensor.coeff_symm (Tensor.diag_smooth M n |>.contDiffAt)) hs
   funext x; rw [← WardBin.leading_tensor _ _ (Tensor.diag_smooth M _ |>.contDiffAt)]; simp_rw [Tensor.homogeneous, WardBin.lead_monomial]; simp
lemma lent_pure {M:Slate G d n}(h:Monic M)(hp:m≤d)(hn:n≤d): (lent M m).val= WardBin.tile (tide M) m:= by
    unfold lent; have he:= Parts.capture (coast_pres h) hp hn; rw [slate_leads (tide_symm h.1)] at he; rw [←he,pieceL_apply]
lemma lent_grade {M:Slate G d n}(h:Monic M)(hp:m≤d)(hn:n≤d): lent M m∈Grade (m,n):= by rw [Labels.pure_grade,lent_pure h hp hn]; exact WardBin.tile_grade ..
lemma tile_bars (M: Slate G d n)(j): conjPol (WardBin.tile (tide M) j)=WardBin.tile (tide M) j:= by
   unfold conjPol WardBin.tile; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [tide_at]; simp
lemma lent_real {M:Slate G d n}(h:Monic M)(hp:m≤d)(hn:n≤d): realBar (lent M m)=lent M m:= by apply Subtype.ext;change conjPol _=_; rw [lent_pure h hp hn]; exact tile_bars M _
lemma pocket_real (M: Slate G d n)(h:Monic M)(hp:m≤d)(hn:n≤d)(j : F.Index): ((Complex.re (pocket F M m j):ℝ):ℂ)=pocket F M m j:= by
    let K:=lent M m; let J:=pocket F M m
    have hv : Complex.conjLIE (J j)=J j:= by
       change star (pocket F _ _ j) = _; unfold pocket; rw [← F.conj_basis,F.coords.symm_apply_apply,lent_real h hp hn]; rfl
    exact Complex.conj_eq_iff_re.mp hv
end YM.FormalBulk08.Pose

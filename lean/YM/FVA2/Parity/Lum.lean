import YM.FVA2.Parity.Shade
/-!
# Sign of reflected Rent & Motto.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Screen
open Function Set Filter Finset Lattice
open MS MS.Koszul MS.Plane MS.Book MS.Native MS.Native.Orient MS.Native.Chart MS.Wind MS.Wind.Leading MS.High MS.Land
open MS.Native.Sew MS.Cylinder MS.Cylinder.Lab MS.Landau MS.Color MS.Native.Paint
open MS.Momentum MS.Menus MS.Native.Wilsonian MS.Arts MS.Outlook MS.Tone MS.Logarithm
open MS.Book.Program MS.Book.Convolve MS.Tone.Frame Hue.Agent Hue.Agent.Kappa Position
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{m n d i:ℕ}{G:Gauge}{p:Team}
local notation "γ"=> grey G Cover
variable (Y:XSpace.Initialize G) (h:Correct p)
local notation "H"=> Press.portDeck G
local notation "ℳ"=> Press.wickInput Y
local notation "g"=> Glyph (Press.portDeck G) d
local notation "ϑ"=> Hue.σ
lemma funds (a:g)(j:a.Bundle) (hi:a.tally j%2≠ a.grade%2): Glyph.hand ℳ a j=0:= by
    cases j with| inl c=> exact (hi rfl).elim| inr c=> rw [Press.stampF]; dsimp only [Press.chip,Sum.elim_inr]; obtain ht:= c.2.isLt.le; have hm:c.2.val%2≠a.grade%2:=hi; rw [Press.odd_empty _ ( Press.primary a.2.2 ) _ _ ht ( Nat.odd_iff.mpr ( show (a.grade- c.2.val)%2=1 from (by omega))), Submodule.coe_zero ]; exact map_zero ( Wheel.red _ )
lemma kit (a:g) (i:ℕ): Hue.only (a.grade+i) (Glyph.gallery ℳ a i).val:= by
    intro j hj; rw [Glyph.gallery, Finset.sum_apply,sum_stack,Finset.sum_apply]; refine Finset.sum_eq_zero (fun k _=>?_ ); unfold levels; by_cases ht:a.tally k%2=a.grade%2; · rw [mask_s, strange _ (by omega)]
    rw [funds Y a k ht,map_zero]; rfl
include h
lemma head (a:g)(x:ℝ)(n:ℕ): Hue.only (a.grade+n) (Glyph.preambleF ℳ p a x n).val:= bill_p x (k:=n) (fun i _=> h.tone i) (fun i _=> kit Y a i) _ (le_refl _)
omit h
abbrev sigma (i:ℕ): ℝ:= (-1)^i
lemma sig (i:ℕ): (sigma i:ℂ)= Hue.σ i:= by simp [sigma,Hue.σ]
local notation "Φ"=> Price H d
def rightS (p n:ℕ)(A:Φ)(i:g) : Poly:= sigma (n+i.grade+p) • A i
lemma forecast {F:Dot G Cover}{u:ℤ} (h:Limit F.val u) : Limit ( γ F ).val u:= fun l hl=> by rw [ tag,Hue.flip_at,h l hl,mul_zero]
def mirrored (T:Power G) : Power G where
    input:= γ ∘ T.input
    polyn:= T.polyn.linear ((γ).restrictScalars ℝ)
    actual x:= ( T.actual x).self_cash ( c:=fun _=> (-1:ℂ)) (by simp)
    calm x:= by intro u; rw [ Function.comp_apply, ← colors, T.calm x u ]
    allowance:=T.allowance
    ranks x:= forecast ( T.ranks x )
def powered (n:ℕ)(A:Power G): Power G:= Favors.bigH ({()} : Finset Unit) (fun _=> sigma n) (fun _=> mirrored A)
def shaded (n:ℕ)(A:Acts H d): Acts H d:= fun i=> ⟨ rightS n i ( A i ).register, powered ( i+n ) ( A i ).proof ⟩
lemma earns (x:g) (v:Acts H d) (y:ℝ) : oil (shaded n v) x i y= ϑ (i+x.grade+n) • oil v x i y:= by unfold shaded oil rightS; rw [ Polynomial.eval_smul,smul_eq_mul, Complex.ofReal_mul,sig ]; rfl
lemma copes (F:Power G)(i:ℕ)(x:ℝ) : ( powered i F ).input x= ϑ i • γ ( F.input x ):= by change (∑ _ ∈ ({()}:Finset Unit), sigma i • ( mirrored F ).input) x=_; rw [Finset.sum_singleton,← sig ]; rfl
include h
lemma rent_pay (v:Acts H d)(x:ℝ) : rentF ℳ p (shaded n v) x i= ϑ (i+n) • γ ( rentF ℳ p v x i ):= by
    unfold rentF; simp only [map_sum,map_smul,Finset.smul_sum,earns]; refine Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl (fun b hb=>?_ )); rw [perfect _ ( head Y h a x b.2 ),smul_eq_mul, smul_smul, smul_smul]; -- scale oil
    obtain he:= Finset.mem_antidiagonal.mp hb; rw [← he]; simp only [Hue.sp]; congr 1; let u:= oil v a b.1 x; calc
     _= ϑ b.1 * ϑ a.grade * ϑ n * u * 1 := (mul_one _).symm
     _= _:= by rw [← Hue.s_id b.2]; ring
lemma motto_pay (v:Acts H d)(x:ℝ): motto p (shaded n v) x i=ϑ (i+n) • γ (motto p v x i):= by
    rw [sky,sky]; change (Spectrum G).Lap ((powered _ _).input _) + _= _; rw [copes,map_smul, ← bumperC,map_add,smul_add,map_sum, Finset.smul_sum ]; apply congr_arg₂ ( ·+· ); rfl
    refine Finset.sum_congr rfl (fun i hi=>?_ ); change ( Spectrum G ).touch _ (( powered (i.2+n) _ ).input _) = _; rw [copes, map_smul, bumperT, mainB p h, map_smul, LinearMap.smul_apply,smul_smul, ← mem_antidiagonal.mp hi ]; simp only [ Hue.sp ]; rw [ show (( ϑ i.1 * ϑ i.2) * ϑ n) * ϑ i.1 = (ϑ i.1 * ϑ i.1 ) * ( ϑ i.2 * ϑ n ) from (by ring), Hue.s_id,one_mul]
lemma score_pay (A:Acts H d)(x:ℝ): scoreF ℳ p (shaded n A) x i=ϑ (i+n) • γ ( scoreF ℳ p A x i ):= by
    simp only [scoreF,Pi.add_apply, rent_pay Y h, motto_pay h, map_add, smul_add]
omit h
lemma tollCap (v:Glyph H d)(x:Acts H d)(hx:FitOrder v (x 0)): FitOrder v ( shaded v.grade x 0 ):= by
    refine ⟨fun D=>?_,fun j hj=>?_ ⟩
    · change Limit ( (powered ( 0+v.grade ) (x 0).proof).input D ).val _; rw [copes]; exact ( forecast (hx.Low D) ).smul _
    change rightS v.grade 0 _ _=_; rw [rightS, hx.Single _ hj]; split_ifs with he; subst j; rw [zero_add, sigma,pow_add ]; rw [ ← mul_pow ]; norm_num; rw [smul_zero]
end YM.FVA2.Parity.Screen

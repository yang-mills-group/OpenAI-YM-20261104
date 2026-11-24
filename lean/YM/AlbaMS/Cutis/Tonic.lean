import YM.AlbaMS.Cutis.Rigid
/-!
# Actual based Hessian inverse & interoperability

Check Reach with Bout resident all cases of n. Mean-size projections used
later, supported Lens weight as given, both orthogonal parts of needed matrices.
`Firm` defines chosen projected full Feynman-K slice; Stokes uses head/basis.
At parameter z finite trivial-saddle *formal*, not claiming uniqueness from a
nonpert shift. Pos on transverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Loft Inlay Inlay.Net Odom Lattice Nexus
variable (G:Gauge)(n: Side)
def rentQ : Fritz (Flit G (Foil n)) (Flit G (Nail n true)) ℝ where
 H:=dotC G (wide n)
 U:=dotC G (longU n)
 symm i j:= by
   have he:(dotC G (wide n))ᵀ= dotC G (wide n):=by simp only [dotC, chip_t,wide_t];
   exact congr_fun (congr_fun he j) i
variable {G n} {P:Precision.ChartRatio G}(hp:Precision.LocalRatio P)(h:Even n.val)
include h
lemma headLots : (waveLots (Root G P n true hp)).Z= dotC G (headD n):=by rw [mantleZ (Rack G n P hp) (walkT n G true) (squall G h P hp true), paidT, normB]; simp only [dotC,chip_t,chip_prod,← chip_scale,headD]
lemma gradLots : (waveLots (Root G P n true hp)).X= dotC G (gradD n):=by rw [mantleX (Rack G n P hp) (walkT n G true) (squall G h P hp true), paidT, paidS,normD]; simp only [dotC,chip_t,chip_prod,← chip_scale,gradD]
lemma headPos : (waveLots (Root G P n true hp)).Z.PosSemidef:=by
  rw [headLots hp h]; unfold headD dotC; rw [chip_scale, ← salute n]; refine Matrix.PosSemidef.smul ?_ (by norm_num)
  simp_rw [← chip_prod,← chip_t]; apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  have he (s:Finset PlaqAxes) : chip G.ColorIndex (∑ i∈s,(tip n i.val.1 i.val.2)ᵀ*tip n i.val.1 i.val.2)=(∑ i∈s,(dotC G (tip n i.val.1 i.val.2))ᵀ* dotC G (tip n i.val.1 i.val.2)):=by
    induction s using Finset.induction_on with|empty=>simp [chip_zero]| @insert i s hv ih=> rw [Finset.sum_insert hv,Finset.sum_insert hv,chip_add, ih]; congr 1; simp only [dotC,chip_t,chip_prod] -- direction?
  rw [he]; exact Matrix.posSemidef_sum _ fun i _=> posSemidef_conjTranspose_mul_self _
lemma metric : (rentQ G n).Normal (waveLots (Root G P n true hp)):= by
  constructor; constructor;
  · rw [Lot.Z_sym,gradLots hp h,headLots hp h]; change dotC G (gradD n)*(dotC G (longU n))ᵀ+dotC G (wide n)*dotC G (headD n)= _; simp only [dotC,chip_t,chip_prod,← chip_add, show gradD n*(longU n)ᵀ +wide n*headD n=1 from projective h, chip_one]
  · rw [gradLots hp h]; simp only [rentQ,dotC,chip_t,chip_prod,guest h,chip_one]
  · rw [gradLots hp h,headLots hp h]; simp only [dotC,chip_prod,E_grad h,chip_zero]
  · rw [gradLots hp h]; simp only [rentQ,dotC,chip_prod,wide_grad h,chip_zero]
  rw [gradLots hp h]; simp only [rentQ,dotC,chip_t,chip_prod]; exact congr_arg _ (orth h) -- maybe t

-- official physical kernel includes projection separately named. n sufficiently even.
omit h in
def gain (G:Gauge)(n:Side)(a:ℝ):= (rentQ G n).scale (a^2)⁻¹ (a^3)⁻¹
lemma owner {a:ℝ}(ha:0<a): (gain G n a).Landau (phys (Root G P n true hp) a):= ⟨(metric hp h).silvers _ _ _ _ (inv_mul_cancel₀ (by positivity)) (inv_mul_cancel₀ (by positivity)),(headPos hp h).smul (sq_nonneg a)⟩
lemma abroad {a:ℝ}(ha:0<a): (gain G n a).boom (phys (Root G P n true hp) a)= dotC G (prop n):=by
  unfold Fritz.boom gain phys Fritz.scale Lot.scale; simp only [rentQ,gradLots hp h]; rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul,smul_smul, mul_inv_cancel₀ (by positivity),one_smul]; simp only [dotC, chip_t, chip_prod,prop]
-- Lift callback for Stokes
variable {R:Type*}[CommRing R][Algebra ℚ R] (T:Tune R)
def locate (hp:Precision.LocalRatio P):= (phys (Root G P n true hp) T.a).beam T.D -- maybe n not inferred
abbrev drive:=Fritz.replic (gain G n T.a) T.D
omit h in
lemma sincerely : (locate (n:=n) T hp).combo= (Root G P n true hp).fair T:= (plaza ..).symm -- h unused
omit [Algebra ℚ R] in
lemma Rosetta : (drive (n:=n) (G:=G) T).Normal (locate T hp):= (owner hp h T.ha).toNormal.beams T.D
end YM.MSBar.Cutis.Winter

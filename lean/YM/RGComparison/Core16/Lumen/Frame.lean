import YM.RGComparison.Core16.Lumen.Planet
import YM.Push.STATIONARY_UNIFORM.Resolvent
/-!
# Hessian rank & native prices in any of our sectors

No bounds on unobserved gauges needed, no approximation of θ tags on other arguments. At g=0
coherent *model* kernel per charge, not taking true action with reset there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial
open Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G:Gauge} {S:Side} {ι k T A D:Type} [Fintype ι] [Fintype k] [Fintype T] [Fintype D]
variable {X:Shelf G A D}
abbrev Wire (G:Gauge)(ι:Type):= ι × G.ColorIndex

def curve {ι:Type} (x:Sky G ι)(e:Wire G ι):ℝ:= G.curvature (x e.1) e.2
section split
-- Counting coordinates.
def vector (v:Wire G ι→ℝ)(i:ι): G.Color:= WithLp.toLp _ fun j=> v (i,j)
def one (u:Wire G ι) : ι → G.Color:=fun i=> if i=u.1 then colors G u.2 else 0

lemma cones (a:G.Color) : ∑ j:G.ColorIndex,a j • (colors G) j=a:=by
    convert! (colors G).sum_repr a using 1
lemma repr (v:Wire G ι→ℝ) : ∑ i,v i • one i=vector v:=by
    funext i
    have hv (j): (vector v i) j=v (i,j):=rfl
    rw [Fintype.sum_prod_type]; simp only [Finset.sum_apply, Pi.smul_apply]
    rw [sum_eq_single_of_mem i (mem_univ _)]; simpa [one,← hv] using cones (vector v i)
    intro j _ h; apply sum_eq_zero; intro b hb; simp [one,Ne.symm h]
lemma cone_height (v:Wire G ι→ ℝ): (∑ i, ‖vector v i‖^2) = ∑ i, (v i)^2:=by
    rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>?_ ; simp [EuclideanSpace.norm_sq_eq,vector]
end split

def shelfH (X:Shelf G A D) (a:A) : Point G D →L[ℝ] Point G D →L[ℝ] ℝ:= fderiv ℝ (fderiv ℝ (X.U a)) 0
lemma higher (Y:Good X)(a:A) : ContDiffAt ℝ ω (X.U a) 0:= Y.payment a _ (by simp [Y.positive.le])
namespace Planet
variable (P:Planet X S ι k T)

def marks (a:k): (ι→ G.Color)→L[ℝ]Point G D := ((0:(ι→ G.Color)→L[ℝ] G.Color)).prod (ContinuousLinearMap.pi fun i=>(P.stem a i).elim 0 fun j=>ContinuousLinearMap.proj j)
omit [Fintype k] [Fintype T] [Fintype ι] [Fintype D] in
lemma mark_price (a:k)(v:ι→ G.Color): P.marks a v=(0,portrait (P.stem a) v):=by
    refine Prod.ext rfl ?_; funext i; rcases he:P.stem a i with _|j <;> simp [portrait,marks,he]; try rfl

def tip (a:k) (i:Wire G ι):= P.marks a (one i)
def plank : Matrix (Wire G ι) (Wire G ι) ℝ:= Matrix.of fun i j=> ∑ a,shelfH X (P.glyph a) (P.tip a i) (P.tip a j)
omit [Fintype T] [Fintype k] [Fintype D] in
lemma inventory (a:k)(u:Wire G ι→ℝ): P.marks a (vector u)= ∑ i,u i • P.tip a i:=by rw [← repr u,map_sum]; simp_rw [map_smul]; rfl
variable {P} (H:P.Steady)
include H
set_option maxHeartbeats 400000
lemma sturdy (v:ι→ G.Color): (∑ i, ‖v i‖^2) ≤ dam X.sector * ∑ a,(1/2:ℝ) * shelfH X (P.glyph a) (P.marks a v) (P.marks a v) := by
   let p:=P.marks; let w:=X.U ∘ P.glyph
   have h a:= higher H.prices (P.glyph a)
   have hs a (y: Point G D): Tendsto (fun t:ℝ=> (t⁻¹)^2*w a (t • y)) Tested.germ (𝓝 ((1/2:ℝ)*shelfH X (P.glyph a) y y)):=by
       have hd (i:ℕ) (hi:i<2): jet (w a) i y=0:= by
           interval_cases i
           · rw [jet_zero]; exact H.prices.zeroth _
           unfold jet; simp only [Nat.factorial , Nat.mul_one]
           rw [iteratedFDeriv_one_apply,show fderiv ℝ (w a) 0=0 from (H.prices.first ..).fderiv]; simp
       have hp: jet (w a) 2 y=(1/2:ℝ)*shelfH X (P.glyph a) y y:= by unfold jet; simp only [Nat.factorial_two,iteratedFDeriv_two_apply,Nat.cast_ofNat,one_div]; rfl
       rw [← hp]; exact ((directions (h a|>.of_le le_top) y).shift hd).tendsto_first
   let Y t:= ∑ a:k,(t⁻¹:ℝ)^2*w a (t • p a v)
   have hy:Tendsto Y Tested.germ (𝓝 _):= tendsto_finsetSum _ fun a _=> hs a (p a v)
   refine ge_of_tendsto (hy.const_mul (dam X.sector)) ?_
   let x (t:ℝ) : Sky G ι:= fun i=> launch ((t : ℝ) • v i)
   have he i:Tendsto (fun t:ℝ=> t • v i) Tested.germ (𝓝 0):= by simpa only [zero_smul] using (((show Continuous fun t:ℝ=> t • v i from by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds)
   have ht:Tendsto x Tested.germ (𝓝 1):=tendsto_pi_nhds.mpr fun i=>by change Tendsto (launch ∘ (fun r:ℝ=> r • v i)) Tested.germ (𝓝 (1:G.El)); exact  launch_zero (G:=G) ▸ launch_cont.tendsto.comp (he i)
   have hk:= H.tickets 0 (show amen X 0 from ⟨le_refl _,H.prices.thick.2.1.le⟩)
   filter_upwards [Tested.eventually_pos,eventually_all.mpr (fun i:ι=> (he i).eventually genesis),ht.eventually ((crisp_open (G:=G) X.δ univ).mem_nhds (show crisp X.δ univ 1 from fun i _=> by simp [H.prices.extent.1]))] with t hy hx hY
   let B:= P.F 0
   have hZ:0<∑ i,B.choices i (x t):=(show ∑ i,B.choices i (x t)=1 from hk.normalized _ ) ▸ zero_lt_one
   obtain ⟨s,-,hs⟩:=Finset.sum_pos_iff_of_nonneg (fun i _=> hk.pos _ i)|>.1 hZ
   have hh (a:k) : B.cost s (x t) a=w a (t • p a v):=by
       change P.cost 0 s (x t) a = X.U (P.glyph a) _; rw [show P.cost 0 s (x t) a= X.U (P.glyph a) _ from H.pay 0 ⟨le_refl _, H.prices.thick.2.1.le⟩ a (x t) s (crisp_negligible _ _ le_rfl (subset_univ _) hY)]
       congr 1
       rw [show p a v= _ from P.mark_price a v]; unfold load; rw [Prod.smul_mk,smul_zero,zero_smul]; congr 1; ext i; rcases h:P.stem a i with _|j <;> simp [portrait,h]; exact congrArg (fun m:G.Color=>m _) (hx j)
   let A : Finset ℕ:= (univ.image (fun i=> separation 0 (P.loc i)))∪ univ.image (fun i=> separation 0 (P.root i))
   let R:=A.sup id
   have hl : neighborsOf B.loc R 0=univ:=top_unique (fun i hi=> (member ..).2 (le_sup (s:=A) (f:=id) (b:=separation 0 (P.loc i)) (mem_union_left _ (mem_image_of_mem _ hi)))) -- parentheses
   have hR : neighborsOf B.band (R+X.sector.b) 0=univ:=top_unique (fun i hi=>(member ..).2 ((le_sup (s:=A) (f:=id) (b:=separation 0 (P.root i)) (mem_union_right _ (mem_image_of_mem _ hi))).trans (Nat.le_add_right ..)))
   have hw:= Base.tax hk (x t) 0 R hs
   change _ ≤ _+ _* ∑ i∈neighborsOf B.band (R+X.sector.b) 0,_ at hw
   unfold threat at hw; rw [hl,hR] at hw; simp at hw
   refine le_trans (b:= t⁻¹^2 * ∑ i,nib (x t) i) ?_ ((mul_le_mul_of_nonneg_left hw (sq_nonneg (t⁻¹))).trans_eq ?_)
   · rw [mul_sum]; refine sum_le_sum (fun i _=>?_)
     have he:= pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm (x t i)) 2; rw [show G.curvature (x t i)= t • _ from hx i,norm_smul,Real.norm_of_nonneg hy.le,mul_pow] at he
     exact le_trans (by rw [← mul_assoc,inv_pow, inv_mul_cancel₀ (pow_pos hy 2).ne',one_mul] : ‖v i‖^2 ≤ t⁻¹^2*(t^2*‖v i‖^2)) (mul_le_mul_of_nonneg_left he (sq_nonneg _))
   change _*(dam X.sector* ∑ i,B.cost s (x t) i)=_
   unfold Y; simp_rw [hh,←mul_sum]; ring
lemma symmetry : (P.plank).IsSymm:= by
    unfold Matrix.IsSymm; ext u v; refine Finset.sum_congr rfl fun x _=> ?_; apply (higher H.prices (P.glyph x)).isSymmSndFDerivAt_of_omega

lemma plucked (u: Wire G ι→ℝ) : u ⬝ᵥ (P.plank *ᵥ u)=∑ a,shelfH X (P.glyph a) (P.marks a (vector u)) (P.marks a (vector u)):=by
    simp_rw [Planet.inventory P _ u,map_sum,_root_.sum_apply,map_smul,_root_.smul_apply,smul_eq_mul]
    unfold plank Matrix.mulVec dotProduct
    simp_rw [Matrix.of_apply,Finset.sum_mul,mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro a _; rw [(show shelfH X (P.glyph j) (P.tip j i) (P.tip j a) = _ from ((higher H.prices (P.glyph j)).isSymmSndFDerivAt_of_omega (P.tip j i) _))]; unfold shelfH; ring

def chip (Y:Prices):=2/dam Y
omit H in lemma chip_pos {Y : Prices}: 0<chip Y:=div_pos (by norm_num) (dam_pos (X:=Y))
lemma forge_piece : Charge (P.plank) (chip X.sector):=by
     intro v
     rw [plucked H]; unfold chip; rw [div_mul_eq_mul_div,div_le_iff₀ dam_pos]; have h:=sturdy H (vector v); rw [cone_height, ←mul_sum] at h; linarith only [h]
lemma forge_plate : P.plank.PosDef:=Charge.positive (forge_piece H) (Matrix.isHermitian_iff_isSymm.mpr <| symmetry H) chip_pos
end Planet
end YM.RGComparison.Core16.Lumen

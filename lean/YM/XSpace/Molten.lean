import YM.XSpace.Flour
/-!
# The suppressed legs with matching-duality curvature at separated marks
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Relief Tide Sail MeasureTheory Gland Chart2 Octave Season Lattice Player Graph3 Chiral Finsupp Outline Pages Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple)(x y z w:Cover) {ι:Type} {a:ι→ℝ}{L:Filter ι}{u v b:E4}
local notation "J" => Name G
local notation "M" => mum W
local notation "Y" => mrs W
local notation "λU" => b_line g W
local notation "λV" => u_line g W
local notation "χz"=> Captain
local notation "δΩ"=> Trace.volume
private lemma ζ₃ (L₀ L₁ L₂:Line G)(P:Stamp G): F2 G (harp L₀*harp L₁*harp L₂) P= read L₂ L₁ L₀ P:= by rw [mul_assoc,ζ_hop,ζ_hop,ζ_line];rfl
-- pay F2 with one or two derivatives
lemma solo (L₀: Line G)(P:Stamp G):
  F2 G (Ξ L₀ (b_w W x)) P=∑ i:J,∑ j:J,∑ k:J, (3*fuel i j k*bstep W g x k L₀) * dual (λU x j) (λU x i) P:=by
  rw [first_strike W g x L₀,bound_up,← clasp P]; simp_rw [map_sum,map_smul,clasp, smul_eq_mul]; unfold b_r; simp_rw [bound_up P,ζ_two]; rfl
lemma doublet (p:PlaqAxes):
 peek G (Vb W x (w,p))=∑ i:J,∑ j:J,∑ k:J,fuel i j k* feet x x x ((M k).origin g) ((M j).origin g) ((M i).origin g) (V3 G (tile p)) w:=by
  unfold Vb b_w; rw [bold g, encoded]; simp_rw [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]; change (∑ i:J,∑ j:J,∑ k:J, fuel i j k*F2 G (harp _*harp _*harp _) _)=_; simp_rw [ζ₃]
variable {x y z:ι→Cover}
variable {c:Shade.Cut}(t:Captain c L a x y z u v b)
local notation "D" => Marked c a x
local notation "π" => Dance (Marked c a x) L a
include t g in
lemma costsT (p:PlaqAxes) : π 6 (fun i w=> peek G (Vb W (x i) (w,p))):=by
  simp_rw [doublet W g]; refine Dance.fin _ _ fun i hi=> Dance.fin _ _ fun j hj=> Dance.fin _ _ fun k hk=>?_ ; exact (essence ((M k).visit g) ((M j).visit g) ((M i).visit g) (systole t.led (vent t.led c x)) (by norm_num) (by norm_num) (by norm_num) (primary (G:=G) p)).const_smul (fuel i j k)
include t in
lemma costsJ (i j:J)(p:PlaqAxes): π 10 (fun t w=> F2 G (Ξ (λV (y t) i) (b_w W (x t))) (Ξ (λV (z t) j) (V3 G (w,p)))):=by -- orientation
  have hh:board D L a x x z:=by have he:= Gland.surface t.led (vent t.led c x) t.grant.xz; exact wheeled (reflected he) -- he x z x; reflected z x x; wheeled => x x z
  simp_rw [Finale.solo W g] -- probably simplify
  refine Dance.fin _ _ fun m _=> Dance.fin _ _ fun n _=> Dance.fin _ _ fun k _=>?_ ; apply tango (B:=1) (Dance.tax (K:=ℂ) t.led (IsBigO.const_mul_left ((M k).starter (Y i) g t) (3*fuel m n k)) (essence ((M n).visit g) ((M m).visit g) ((Y j).visit g) hh (by norm_num) (by norm_num) (by norm_num) (primary p))) zero_le_one; refine Eventually.of_forall fun q w h=>?_ ; rw [encoded w,one_mul]; exact le_refl _
include t in
lemma costsL (i j:J)(p:PlaqAxes): π 10 (fun t w=> peek G (Ξ (λV (y t) i) (Ξ (λV (z t) j) (Vb W (x t) (w,p))))):=by
  unfold Vb; simp_rw [Graph3.mid W g _ _ _ _ (V_votes _)]; -- read V_votes namespace Graph3.
  apply Dance.add (costsJ W g t i j p) (costsJ W g t.hop.turn j i p)
include t in
lemma costsM (p:PlaqAxes) : π 15 (fun i w=> bottom W g (y i) (z i) (Vb W (x i) (w,p))):=by
  unfold bottom; simp only [LinearMap.sum_apply,LinearMap.smul_apply]; refine Dance.fin _ _ fun i _=> Dance.fin _ _ fun j _=>?_ ; simp_rw [slows]; apply Dance.const_smul; let h:= (Y i).receipt (Y j) g t.turn rfl; apply Dance.add (Dance.tax (K:=ℂ) t.led (IsBigO.const_mul_left h 4) (costsL W g t i j p)) ?_; simp_rw [pow_two]; exact (Dance.tax (K:=ℂ) t.led (IsBigO.const_mul_left (gowns h h) 2) (costsT W g t p)).order t.led (by norm_num) -- order args
include t in
lemma mainSe (p:PlaqAxes): Named L a 14 (fun i=>∑' w:Cover, outer W g c (a i) (x i) (y i) (z i) (w,p)) 0:=by
  let f i w:= outer W g c (a i) (x i) (y i) (z i) (w,p); have he(i:ι)(w:Cover)(h:0<a i): 1-Shade.pace c (a i) (w-x i)=(↑(strip c (a i) (w-x i)):ℂ):=by rw [← store c _ _ h]; push_cast;rfl -- strip unfolded?
  apply Named.low _ t.led; apply pull t.led; apply Dance.lift (S:= D); swap
  · refine t.led.good.mono fun i hi w h hh=>h ?_; change strip c (a i) (w-x i)=0 at hh; unfold outer; dsimp only; rw [he _ _ hi,hh]; simp
  refine tango (B:=1) (costsM W g t p) zero_le_one (t.led.good.mono fun i hi w _=>?_); unfold outer fund; dsimp only; rw [he i w hi,one_mul, norm_mul,Complex.norm_real]; exact mul_le_of_le_one_left (norm_nonneg _) (strip_norm ..)
end YM.XSpace.Finale

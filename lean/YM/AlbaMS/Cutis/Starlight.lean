import YM.AlbaMS.Cutis.Wires

/-!
# orbit B to studio pulse. squashed, mean-profile lift

Works for any side (relations prove at even sides only); full symbol covariance
in inversion quotient is `F.spred`, mean projected. Based checks use matrices
*without* assumptions on T scaling or momentum support: Wick evaluates in fixed
rank stencils. Position Δ_r-type path after.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter IsNilpotent LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Coil Loft Inlay Inlay.Net Odom Lattice Nexus
variable {X E B V W R S : Type*}[Fintype E][Fintype B][Fintype V][Fintype W][CommRing R][CommRing S]
omit [Fintype V][Fintype W] [Fintype E] [Fintype B] in
lemma grab {ρ:Place E B→Bool}{σ:Place V W→Bool} (s:Finset (Place E B)) {F G:Place E B→Place V W→ R} (h:Routes ρ σ F)(H:Routes ρ σ G)(hv: F=G) : shot s F h=shot s G H:=by subst G; rfl
namespace Wire
variable {G:Gauge}{Ω:Net E B}{H:Net V W}(u:Receipt G Ω H)(P: Wire E B V W R)
omit [Fintype E][Fintype B] in
def register : Wire (Flit G E) (Flit G B) (Flit G V) (Flit G W) ℝ:=⟨Φ u,Φ u,Ψ u, Matrix.of fun i j=>u.rate i.1 * Ψ u i j⟩
omit [Fintype V][Fintype W][Fintype E][Fintype B] in
lemma reg_eq : (register u).fee=u.skein:=by funext i j; rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;> rfl
omit [Fintype V][Fintype W] in
lemma crosses (T:Tune R) : T.crossT u=((register u).atlas T.D).firm:=by apply grab; funext i j; symm; rw [Wire.linked, reg_eq]
omit [Fintype V][Fintype W] in
lemma shoot_n (X:Floor E B R)(h:FinRank X): FinRank (P.firm X):=⟨_,h.choose_spec.shoots⟩
variable {J I : Type*}[Fintype J][Fintype I]
omit [Fintype E] [Fintype B] in
lemma cribCompose (L:Wire V W X J R) [Fintype X] (F:Fritz X J R): (P.compose L).crib F=P.crib (L.crib F):=by unfold crib compose; congr 1 <;> simp only [Matrix.mul_assoc,Matrix.transpose_mul]
end Wire
namespace Winter
-- Squash independent variables.
abbrev Env (G:Gauge)(n:Side):= Flit G (Foil n)
abbrev Sand (G:Gauge)(n:Side):= Flit G (Nail n true)
variable (G:Gauge)(n:Side)(a:ℝ)
def extoll : Fritz (ink1 G n) (ink0 G n) ℝ where
 H:=(a^2)⁻¹ • dotC G (Winter.W n+ Winter.W n * aura n)
 U:=(a^3)⁻¹ • dotC G (Winter.U n+ aura n* Winter.U n)
 symm i j:=by
   let Q:= Winter.W n+ Winter.W n*aura n; have he : Qᵀ=Q:=by unfold Q; simp only [transpose_add,transpose_mul,WT,aura_t,WW]
   have hh : ((a^2)⁻¹ • dotC G Q)ᵀ = (a^2)⁻¹ • dotC G Q := by rw [transpose_smul]; simp only [dotC, chip_t, he];
   exact congr_fun (congr_fun hh j) i
def squash : Wire (Env G n) (Sand G n) (Env G n) (Sand G n) ℝ:=
    ⟨1 - dotC G (Winter.prop n), dotC G (Winter.prop n),1,0⟩
def lineWire : Wire (ink1 G n) (ink0 G n) (Env G n) (Sand G n) ℝ:=
    Wire.register (walkT n G true)
def passage : Wire (ink1 G n) (ink0 G n) (Env G n) (Sand G n) ℝ:=
    { lineWire G n with c:=dotC G (run n) }

lemma squash_map {P:Precision.ChartRatio G}(hp:Precision.LocalRatio P)(h:Even n.val)(ha:0<a): (squash G n).crib (gain G n a)=gain G n a:=by
  let X:=phys (Root G P n true hp) a; let F:=gain G n a; have he:= (owner hp h ha).toNormal; have hc:F.Normal X:=he; have hh:F.boom X=dotC G (Winter.prop n):=abroad hp h ha
  let Y:=F.boom X; unfold Wire.crib squash; conv_rhs=> rw [show gain G n a= { H := F.H,U:= F.U,symm:=F.symm } from rfl]
  congr 1
  · simp only [← hh,transpose_sub,transpose_one]; change (1-Y)*F.H*(1-Yᵀ)= F.H; rw [show Yᵀ=Y from hc.orthog,hc.first_dot,hc.first_oth]
  change dotC G (Winter.prop n)*F.U*(1:Matrix (Sand G n) (Sand G n) ℝ)ᵀ= _; rw [← hh,hc.tapK,transpose_one, Matrix.mul_one]; rfl
-- remove hp argument for primary equality
lemma squash_price (h:Even n.val)(ha:0<a): (squash G n).crib (gain G n a)=gain G n a:=by obtain ⟨P,hp⟩:= LocalH.actual G; exact squash_map G n a hp h ha
lemma redraw (h:Even n.val) : (passage G n).crib (gain G n a)=extoll G n a:=by
  have ha : (passage G n).a=dotC G (thorn n):= paidT ..; have hk:(passage G n).k=dotC G (thorn n):= paidT ..
  unfold Wire.crib extoll; congr 1
  · simp only [ha, gain,Fritz.scale,rentQ,dotC,chip_t]; rw [Matrix.mul_smul,Matrix.smul_mul]; simp only [chip_prod, cash_A h]
  simp only [hk,gain,Fritz.scale,rentQ]; change dotC G (thorn _)* (_ • dotC G (longU n)) * (dotC G (run _))ᵀ=_; rw [Matrix.mul_smul,Matrix.smul_mul];simp only [dotC, chip_t, chip_prod, cash_C h]
def lead := (lineWire G n).compose (squash G n)
def spark := (passage G n).compose (squash G n)
lemma lore_A : (lead G n).a= dotC G (thorn n*(1-Winter.prop n)):=by change Φ _ *(1- dotC _ _)=_; rw [paidT]; unfold dotC; rw [← chip_prod,chip_sub,chip_one]; -- after chip_sub then prod simp
lemma lore_K : (lead G n).k=dotC G (thorn n * Winter.prop n):=by change Φ _ *dotC _ _=_; rw [paidT]; exact chip_prod ..
lemma lore_S : (lead G n).l=0:=by apply Matrix.mul_zero
lemma realize (T:Tune R)(h: Even n.val)(X:Heave G (Edge (Site n)) (Site n) R) [Algebra ℚ R](ht:FinRank X):
    Fritz.eval ((extoll G n T.a).replic T.D).hop X = Fritz.eval (drive (G:=G) (n:=n) T).hop (((spark G n).atlas T.D).firm X):=by -- root real bank. W hop projection. bool.
  rw [← Wire.draws _ _ _ ht]; congr 1; rw [spark,← Wire.plays,Wire.cribCompose,squash_price G n T.a h T.ha, redraw G n T.a h] -- maybe congr
end Winter
end YM.MSBar.Cutis

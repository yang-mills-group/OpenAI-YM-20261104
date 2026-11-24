import YM.MS.Orbit.Offset
/-!
# Linear level; transforms for series convolution at frozen configuration index.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit.LogReal
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{I A W E: Type}{L:I→Side}[Fintype A]{X Y:Series A}{n:ℕ}{b:Bool}{Z: Lines A}{p:Sector A} {i:I}
def visitT (Z:Lines A)(p:Sector A) : OM A→ₗ[ℂ] OM A→ₗ[ℂ] OM A:={
   toFun F:= { toFun:= TypeTouch p Z F
               map_add' _ _:= funext fun _=> link_add ..
               map_smul' _ _:= funext fun _=> link_smul .. }
   map_add' _ _:= LinearMap.ext fun _=> funext fun _=> link_add_left ..
   map_smul' _ _:= LinearMap.ext fun _=> funext fun _=> link_smul_left .. }
def rung (Z:Lines A)(p:Sector A)(j k:ℕ): Series A →ₗ[ℂ] Series A→ₗ[ℂ] OM A:={
   toFun F:= { toFun := fun H=>Level p Z F H j k
               map_add' U V:= by unfold Level pathU; simp_rw [show TypeTouch p Z=fun F H=> visitT Z p F H from rfl,Pi.add_apply,map_add,Finset.sum_add_distrib]
               map_smul' u H:= by unfold Level pathU; simp_rw [show TypeTouch p Z=fun F H=>visitT Z p F H from rfl,Pi.smul_apply,map_smul,Finset.smul_sum]; rfl }
   map_add' U V:= by apply LinearMap.ext; intro F; change Level p Z (U+V) F j k=Level p Z U F _ _+Level p Z V F _ _; unfold Level pathU; simp_rw [show TypeTouch p Z=fun F H=> visitT Z p F H from rfl,Pi.add_apply,map_add, LinearMap.add_apply,Finset.sum_add_distrib]
   map_smul' u H:= by apply LinearMap.ext; intro F; change Level p Z (u • H) F j k=u • Level p Z H F _ _; unfold Level pathU; simp_rw [show TypeTouch p Z=fun F H=> visitT Z p F H from rfl,Pi.smul_apply,map_smul,LinearMap.smul_apply, Finset.smul_sum ] }
lemma counterpart (hi:0<n)(h:∀ i j,TypeTouch p Z ( X i ) ( Y j )= TypeTouch p Z ( Y j ) ( X i )): Level p Z X Y n 1=Level p Z Y X n 1:= by
   let f(i j:ℕ):=TypeTouch p Z ( X i ) ( Y j ); let g(i j:ℕ):= TypeTouch p Z ( Y i ) ( X j ); have he:(∑ i∈antidiagonal n,f i.1 i.2)=∑ i∈antidiagonal n,g i.1 i.2:= by simp_rw [ f,g,h ]; exact Finset.Nat.sum_antidiagonal_swap (f:= fun i=>g i.1 i.2)
   rw [ Tone.Frame.canon_corner f n hi,Tone.Frame.canon_corner g n hi ] at he; change f 0 n+f n 0+Level _ _ X Y n 1=g 0 n+g n 0+Level _ _ Y X n 1 at he; rw [show f 0 n= g n 0 from h 0 n,show f n 0=g 0 n from h n 0, add_comm (g 0 n)] at he; exact add_left_cancel he -- actually add_left canc?
variable {B:Rake.Site G I}{F H:Rake.Site G I}{ P:Planet G I}{X': H_defect G I}{u v:Faces I}
local notation "Ω"=> enterV L b
local notation "Γ"=> σbranch (G:=G) ( n:=dimT L i )
abbrev Panels (L:I→Side)(b:Bool)(i:I)(B:Rake.Site G I): Series ( FixedMode G (dimT L i)):= (PayB L b i) ∘ B
abbrev Ag (L:I→Side)(b:Bool)(i:I)(v:Faces I)(B:Rake.Site G I): Series ( FixedMode G (dimT L i)):= (PayA L b i v) ∘ B
omit [Fintype A] in
lemma level_b (h:Glow P)(hp:∀ k,Knits ( B k ))(hm:∀ k,StandGuard L ( B k ) i)(n j:ℕ): Level Γ (zoneP L b P i) (Panels L b i B) (Panels L b i B) n j=PayB L b i (pathU (expJ P) n j B B):= by
    unfold Level pathU; rw [map_sum]; exact Finset.sum_congr rfl fun i hi=> Φ_BB ( hp _|>.1 ) (hp _|>.1 ) h (hm _) b
omit [Fintype A] in
lemma level_ba (h:Glow P)(hp:∀ k, Knits (B k))(hm:∀ k,StandGuard L (B k ) i)(he:∀ k,Knits (F k))(n k:ℕ): Level Γ (zoneP L b P i) (Panels L b i B) ( Ag L b i u F ) n k=PayA L b i u ( pathU (expJ P) n k B F ):= by unfold Level pathU; rw [map_sum]; exact Finset.sum_congr rfl fun i hi=> Φ_BA (hp _|>.1) (he _|>.1) h (hm _) b
omit [Fintype A] in
lemma level_a {a:I}(h:Glow P)(hp:∀ k, Knits (H k))(i j:ℕ): Level (σbranch (G:=G) ( n:=dimT L a )) (zoneP L b P a) (Ag L b a u F) (Ag L b a v H) i j= PayA L b a v ( pathU (zip2 Ω P u v) i j F H ):= by unfold Level pathU; rw [map_sum]; exact Finset.sum_congr rfl fun i hi=> Φ_AA (hp i|>.1) h -- unused shadow a fail
abbrev Helm (L:I→Side)(b:Bool)(i:I)(X:H_defect G I)(x:Half):= Ag L b i (loci (enterV L b) x) ( X x )
def states (L:I→Side)(b:Bool)(x:H_defect G I)(i:I):= ∑ j:Half, Helm L b i x j
omit [Fintype A] in
lemma level_d (h: Glow P)(hp:∀ k, Knits (F k))(n k:ℕ): Level Γ (zoneP L b P i) ( states L b X' i ) ( Ag L b i u F ) n k= PayA L b i u ( foam Ω P X' F u n k ):= by
    let T:=rung (zoneP L b P i) Γ n k; change (T (states L b X' i) (Ag L b i u F))=_; unfold foam states; rw [map_sum (PayA L b i u), map_sum T, LinearMap.sum_apply ]; exact Finset.sum_congr rfl fun j _=>(level_a (F:=X' j) ( u:=loci Ω j ) h hp n k )
end YM.MS.Orbit.LogReal

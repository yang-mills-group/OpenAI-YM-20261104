import YM.FVA2.Lambda.Shuffles
/-!
# orientation for closed trace and color index pairing

 Inner k on A1→A2, outer q on closed trace. Units K_BV half by cost, package ghost signs before radial. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Area
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open Complex (I)
open Canvas (quad high top_quad line4 triple upperquad trigger)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))
-- For Σ replacement all Axis.* j color same.Support explicit forms.
abbrev W₀ (i:Axis)(c:G.ColorIndex):BH G:= ((gauge i),c)
abbrev U₀ (i:Axis)(c:G.ColorIndex):BH G:= ((anti i),c)
abbrev C₀ (c:G.ColorIndex):BH G:= (ghost,c)
abbrev S₀ (c:G.ColorIndex):BH G:= (gaugeC,c)
-- assign support (BH)^2 exactly normalized line
variable (D E:ℝ→ℝ)(F H:Law G)(l r: List (Lane4 G))(i j:BH G)(p:QP)
lemma paircol (f:BH G→ BH G→ℂ) : (∑ i,∑ j,line4 G D i j p * f i j)=∑ c:G.ColorIndex, ((∑ a:Axis,∑ b:Axis, (↑( D p.sq * Landau.precision a b p ):ℂ) * f ( W₀ a c ) ( W₀ b c )) + (∑ a:Axis, (↑( D p.sq * p.sq * p a):ℂ) * I * f ( U₀ a c ) ( C₀ c ))+(∑ a:Axis, (↑( D p.sq * p.sq * p a):ℂ)* I * f (C₀ c) ( U₀ a c ))) := by
    unfold line4 Shells.link Landau.choir; rw [ Fintype.sum_prod_type, Finset.sum_comm ]; apply Finset.sum_congr rfl; intro c _; simp [ Fintype.sum_prod_type,Fintype.sum_option, ite_mul, Shells.MK ]; rw [Finset.sum_add_distrib]; unfold W₀ U₀ C₀; abel
lemma contact (u:ℝ→ℝ)(p:QP)(l r:List (Lane4 G)) (hn: p= -net l): Bead.attach u F H l r=∑ i,∑ j,line4 G u i j p*(cross (parity j) (degree Ψ l)* F ((i,p)::l)*H ((j,-p)::r)):= by subst p; unfold Bead.attach Bead.summit; simp only [mul_assoc]
-- no G if high A1=triple by recurrence? later. tail argument s L. braces.external sign = cross(odd b,degree left tail)
abbrev piece (D E:ℝ→ℝ)(F H:Law G)(p:QP)(l r:List (Lane4 G))(i j:BH G):ℂ:= line4 G D i j p * ( cross (parity j) (degree Ψ l) * Bead.attach E F H ((i,p)::l) ((j,-p)::r))
def first (D E:ℝ→ℝ)(F H:Law G)(p:QP) (l r:List (Lane4 G)):ℂ:= ∑ i,∑ j,piece D E F H p l r i j
lemma second : ( ∑ i, ∑ j,line4 G D i j p*( cross (parity i) ((parity j) ^^ degree Ψ l) * Bead.attach E F H ((j,-p)::l) ((i,p)::r)))= Area.first D E F H (-p) l r:= by
    unfold Area.first; rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; unfold piece; rw [show line4 G D i j (-p)=_ from (show Heat.Reverse (line4 G D) parity from Shells.flipped G D ) i j p ]; cases parity i <;> cases parity j <;> cases degree Ψ l <;> simp
lemma cyclic (x y:Lane4 G)(he:x.2+y.2=0) : Flux.trc (line4 G D) p (quad G E (triple G) (triple G)) [x,y]= 2*( (Area.first D E (triple G) (triple G) p [x] [y])+(Area.first D E (triple G) (triple G) (-p) [x] [y]) ) := by
    rw [ ← second ]; unfold Area.first; simp_rw [Flux.at_trc, (show ∀ i j:BH G, quad G E (triple G) (triple G) [(i,p),(j,-p),x,y]=_ from fun i j=> Bead.expand4 E (i,p) (j,-p) x y (by simp) he) ]; simp only [← Finset.sum_add_distrib, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; unfold piece; simp only [degree_cons,degree_nil,Bool.xor_false,field]; ring
end YM.FVA2.Lambda.Area

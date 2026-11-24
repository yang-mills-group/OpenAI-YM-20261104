import YM.MS.Orbit.Reset
/-!
# Evaluate Φ on finite mesh by transfer through stage. Tess. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{P: Latch.Edge G}{F H:Law G}{n:Side}{x:Lengths G}
abbrev Vμ (F:Law G)(n:Side):= rentS G n F -- λ reserved replace
lemma point (F:Law G)(w:Legs (FixedMode G n)): Vμ F n w=F (stage w):=rfl
local notation "Z"=> field ( parity ( A:=Axis ) ( C:=G.ColorIndex))
abbrev faceκ (b:Bool)(n:Side)(P:Latch.Edge G):= if b then imageW (iota G n) (mat n P) else mat n P -- image only
abbrev Omega (A:Type)[Neg A](b:Bool):A→A:= if b then id else Neg.neg -- image yes
lemma barkU (F:QP→ℂ)(n:Side): (∫ i,F i∂ σcap n)= ∑ i:Site n,scaleZ n * F (Coord i):= by rw [siteI,totalW,Finset.smul_sum]; rfl
lemma pCharge (p:Site n)(b:Bool): congrQ ( Coord ( Omega (Site n) b p ) ) ( Opp b (Coord p) ):= by cases b; exact ( ξ_neg .. ).sym; exact congrQ.normal _
lemma κFocus {E:Type}[AddCommMonoid E][Module ℂ E](b:Bool) (V: FixedMode G n→FixedMode G n→ E): (∑ i: FixedMode G n,∑ j:FixedMode G n, faceκ b n P i j • V i j )= ∑ p:Site n,∑ i:BH G,∑ j:BH G,(scaleZ n*ηbone b P i j (Coord p)) • V (i,p) (j,Omega _ b p):= by cases b; exact StraightFocus V; exact ImageFocus V
lemma on_frame (b:Bool)(F:Than G n): frame ( faceκ b n P ) F=∑ p:Site n,∑ i:BH G,∑ j:BH G,(scaleZ n*ηbone b P i j (Coord p)) • diffPair (i,p) (j,Omega _ b p) F:= by
   unfold Cog.frame; simp only [LinearMap.sum_apply,LinearMap.smul_apply]; exact κFocus b (fun i j=> diffPair i j F)
lemma compete (w:Legs (FixedMode G n))(p:Site n) (i j:BH G)(h:Speaks F)(b:Bool): Vμ F n ((i,p)::(j,Omega _ b p)::w)= F ((i,Coord p)::(j,Opp b (Coord p))::stage w):= h _ _ (.cons ⟨rfl,congrQ.normal _⟩ (.cons ⟨rfl,pCharge p b⟩ ( asc _ )))
-- anchor and bulk.H_T
abbrev Φa (A:Cover)(p:Site n): ℂ:= Bloch.cell (wrap n A) p
lemma φ_c (A:Cover)(p:Site n): Φa A p=be A (Coord p):= by unfold be; rw [dual_cell]; exact Bloch.cell_duality ..
lemma φ_s (w:Legs (FixedMode G n))(A:Cover): Φa A (net w)=be A (net (stage w)):= by obtain he:= φ_per A (θ_net w); exact ( φ_c .. )|>.trans he.symm -- be now gone.Bad
lemma φ_other (A:Cover)(x: Site n)(b:Bool): Φa A (Omega (Site n) b x)=Φa (taste b A) x:= by
    cases b; · unfold Φa; rw [Bloch.cell_duality (wrap n _) (Omega _ _ _)]; change Bloch.cell (-x) _=Bloch.cell (wrap n (-A)) x; rw [map_neg]; change Bloch.cell (-x) _= Bloch.cell (-wrap n A) x; rw [Bloch.cell_duality,Bloch.cell_inverse,Bloch.cell_duality (-wrap n A), Bloch.cell_inverse, Bloch.cell_duality x]; -- $map_neg not simp Ω
    rfl
def chase (n:Side)(A:Cover): Op (FixedMode G n) ℂ:={
   toFun F:= fun w=> Φa A (net w)*F w
   map_add' F H:= by ext; exact mul_add ..
   map_smul' a F:= by ext; exact mul_left_comm .. }
abbrev anchor (G:Gauge)(n:Side)(A:Cover): Law G→ₗ[ℂ] Than G n:= (chase n A).comp (rentS G n)
abbrev brightness (n:Side):= (scaleZ n)⁻¹
lemma lightW (n:Side): scaleZ n*brightness n=1:= mul_inv_cancel₀ (by unfold scaleZ; exact_mod_cast (ν_pos n).ne')
def gate (A:Type)(n:Side): Op (Mode A (Site n)) ℂ:={
   toFun F:=fun w=> if net w=0 then F w else 0
   map_add' F H:= by ext; split <;> simp [ * ]; -- simp cleanup
   map_smul' u F:= by ext; split <;> simp [*] }
abbrev Bulk (G:Gauge)(n:Side) : Law G→ₗ[ℂ] Than G n:= brightness n • (gate (BH G) n).comp ( rentS G n )
lemma bulkZ (F:Law G)(w:Legs ( FixedMode G n)): Bulk G n F w= if net w=0 then brightness n* Vμ F n w else 0:= by unfold Bulk; simp only [LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply,smul_eq_mul]; unfold gate; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; split <;> simp [ Vμ, * ]
lemma chase_now (A:Cover)(w:Legs (FixedMode G n)): anchor G n A F w= Φa A (net w)* Vμ F n w:= rfl
lemma Gps (F:Law G)(n:Side): Conserved (Bulk G n F):= fun w hw=> by rw [bulkZ]; exact if_neg hw
end YM.MS.Orbit

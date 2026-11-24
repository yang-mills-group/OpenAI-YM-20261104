import YM.FormalBulk08.Sable.Skip
import YM.FormalBulk08.Quire.Audience

/-! Pre salary for D or H at polynomial payment (with δ measured before blocking). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels Dawn Palm PowerSeries
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {X:Type}{m d D l u j t r e:ℕ}{η A B C:ℝ}{K: KernelChoices}{P:Patch}{a:Loc G 1}
structure OfficeK (K:KernelChoices)(F:Frame G d)(a:Loc G 1)(u:ℕ)(Z:Flight j t)(U:Lodge Z.patch)(e r l D:ℕ)(μ X:ℝ):Prop where
   claim:∀ T: Anthem D G,Clef a T l→∀ B:ℝ,Pawn a u T e B→(∀ i, ‖coeff e (echo F T i)‖≤ B) → ∀ A:ℝ,0≤A→ (∀ p,Knoxville (grain (fame _) 1) u (0,a) (T p e r) (A*‖p‖)) →∀ hL:2≤Z.L.val,(∀ i:Letter F,slots F i=r→ ‖pearlJ F (blade Z K U T d e r hL (inside F i D)) (mint F i)‖ ≤ X*B) ∧∀ p, Knoxville (grain (fame _) 1) u (0,a) (blade Z K U T d e r hL p) ((μ*A+X*B)*‖p‖)
lemma office_raise {Z:Flight j t}{U:Lodge Z.patch}{F:Frame G d}(x h:ℝ)(hp:OfficeK K F a u Z U e r l D x A)(hv:A≤B)(he:x≤h): OfficeK K F a u Z U e r l D h B:= by
     refine ⟨fun Y hY b hg hz a' ha' H hL=>?_⟩;obtain ⟨z,t⟩:= hp.claim Y hY b hg hz a' ha' H hL; exact ⟨fun i hi=>(z i hi).trans (mul_le_mul_of_nonneg_right hv hg.1),fun p=>(t p).mono (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right he ha') (mul_le_mul_of_nonneg_right hv hg.1)) (norm_nonneg _))⟩
structure Buried (K:KernelChoices)(F:Frame G d)(o:Loc G 1)(D E R u j t:ℕ)(P:Patch)(V:Lodge P)(B:ℝ):Prop where
   plus:0≤B
   bill:∀ Z:Flight j t,∀ U:Lodge Z.patch,∀ h:Z.patch=P,h ▸ U=V→∀ e≤E,∀ r≤R+E,∀ l≤R,OfficeK K F o u Z U e r l D (Dove.Mulct Z.L) B
lemma buried_raise {F:Frame G d}{U:Lodge P}(h:Buried K F a D e r u j t P U A)(p:A≤ B) : Buried K F a D e r u j t P U B:= ⟨h.plus.trans p,fun Z S _ hV i hi Y hs k hp=>office_raise _ _ (h.bill Z S _ hV i hi Y hs k hp) p le_rfl⟩
def Cairn (K:KernelChoices)(F:Frame G d)(a:Loc G 1)(D E R u j t:ℕ)(B:ℝ):Prop:= ∀ P:Patch,B≤(P.L.val:ℝ) →∀ V:Lodge P,∃ C:ℝ,Buried K F a D E R u j t P V C
lemma preCairn (K:KernelChoices)(F:Frame G d)(H:Hol G)(o: Loc G 1)(D E R u j t:ℕ)(h:d<D)(hj:4≤j)(hp:d+1≤j-2)(ht:4≤t)(hs:(d+1)*(d+1)≤u) :∃ B:ℝ,0≤B ∧Cairn K F o D E R u j t B:= by
     obtain ⟨σ,C,hσ,hC,h'p,-⟩:= may_use G K j t hj ht
     let I:=Fin (E+1)×Fin (R+E+1)×Fin (R+1)
     choose! B hB Hx using fun i:I=>raiseB o F H i.2.1.val i.2.2.val i.1.val D h hj hp ht hσ hC.le hs K
     let B':=∑ i,B i
     refine ⟨B',Finset.sum_nonneg (fun i _=> hB i),fun P hz V=>?_⟩; choose! C' hc' H' using fun i=>Hx i P ((Finset.single_le_sum (f:=B) (fun j _=>hB j) (Finset.mem_univ i)).trans hz) V
     let X:=∑ i,C' i; refine ⟨X,Finset.sum_nonneg (fun _ _=>hc' _),fun Z U h hv e he r hr l hl=>?_⟩
     let z:I:=(⟨e,by omega⟩,⟨r,by omega⟩,⟨l,by omega⟩); exact office_raise _ _ (show OfficeK K F o u Z U e r l D (Dove.Mulct Z.L) (C' z) from ⟨H' z Z U _ hv (h'p Z)⟩) (show C' z≤ X from Finset.single_le_sum (fun i _=>hc' i) (Finset.mem_univ z)) le_rfl
end YM.FormalBulk08.Sable

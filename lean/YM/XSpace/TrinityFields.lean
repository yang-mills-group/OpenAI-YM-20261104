import YM.XSpace.Prom
/-!
# The actual two composite labels and open degree at order one
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chiral
open Function Set Filter Lattice Chart2 Trace Maxwell Maxwell.Free Maxwell.Wick Structure1 Normalize Source Source.Drops Wilson Mu Lows Stall Outline Next.Rank.Normal Contraction MvPolynomial Pages
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}{d n:ℕ} {H:Hol G}
def Bfield (G:Gauge) : HP G 6:= ⟨B G,B_paint,B_grade⟩
def Ufield (G:Gauge) : HP G 4:= ⟨U G,(by rw [understand]; apply Submodule.smul_mem; exact Submodule.sum_mem _ fun i _=> team_label _ _ le_rfl),U_grade⟩
lemma b_rank : Hom (B G) 3:= by
  have he (p : Name G): Hom (plusV p) 1 := symbol_hom (arm true p) (fun _=> (1:ℕ)); unfold B; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; apply IsWeightedHomogeneous.sum; intro k _; exact Submodule.smul_mem (rank 3 _) _ (((he i).mul (he j)).mul (he k))
lemma u_rank : Hom (U G) 2:=by
  have he (p : Name G): Hom (minusV p) 1 := symbol_hom (arm false p) (fun _=> (1:ℕ)); unfold U; apply (rank 2 _).smul_mem; apply Submodule.sum_mem; intro i _; exact (he i).mul (he i)
lemma b_turn : XSpace.Taylor.mirror (Maxwell.Slot G) (B G)= -B G:=by rw [Taylor.parity_sign (B G) (n:=3) b_rank]; norm_num
lemma u_turn : XSpace.Taylor.mirror (Maxwell.Slot G) (U G)= U G:=by rw [Taylor.parity_sign (U G) (n:=2) u_rank]; norm_num
lemma b_real : realForm (B G)= B G:=by unfold B plusV spark; simp only [map_sum, real_scale,map_mul, real_symbol,fuel_real]
lemma u_real : realForm (U G)= U G:=by unfold U minusV spark; simp [map_sum,real_symbol,real_scale]

variable (g:G.Simple)(W:Initialize G)
local notation "A" => W.surveys 6
local notation "M" => W.surveys 4
abbrev b_line (x:Cover)(u:Name G):= cable g (W.surveys 6) true u x
abbrev u_line (x:Cover)(u:Name G):= cable g (W.surveys 4) false u x
abbrev b_s (x:Cover)(u) := brace (W.surveys 6) true u x
abbrev u_s (x:Cover)(u) := brace (W.surveys 4) false u x
abbrev b_r (x:Cover)(u):= harp (b_line g W x u)
abbrev u_r (x:Cover)(u):= harp (u_line g W x u)

def b_1 (x:Cover): Stamp G:= P1 (W.surveys 6) x (On.lifting (B G))
def u_1 (x:Cover): Stamp G:= P1 (W.surveys 4) x (On.lifting (U G))
open Foundation
lemma bold (x:Cover): slack W x (Bfield G)=∑ i:Name G,∑ j:Name G,∑ k:Name G, fuel i j k • (b_r g W x i * b_r g W x j * b_r g W x k):=by
  unfold slack Prelude.enter0; rw [← move_reel,Price.preparedV]; change P0 _ x (On.lifting (B G))=_; unfold B; simp_rw [map_sum,map_smul,map_mul,π0]; simp_rw [show plusV (G:=G)=spark (G:=G) true from rfl,translatedL g]
lemma under (x:Cover): slack W x (Ufield G)=(2:ℂ)⁻¹ • ∑ i:Name G,u_r g W x i * u_r g W x i:=by
  unfold slack Prelude.enter0; rw [← move_reel,Price.preparedV]; change P0 _ x (On.lifting (U G))=_; unfold U; simp_rw [map_smul,map_sum,map_mul,π0, show minusV (G:=G)=spark (G:=G) false from rfl,translatedL g]

lemma underneath (x:Cover): u_1 W x=∑ i:Name G,u_s W x i*u_r g W x i:=by unfold u_1 U; simp_rw [map_smul,map_sum,map_mul,stimulated,π1,π0, show minusV (G:=G)=spark (G:=G) false from rfl, translatedL g,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; change _ • (u_s W x i*u_r g W x i+u_r g W x i*u_s W x i)=_; rw [mul_comm (u_r ..), ← two_smul ℂ,inv_smul_smul₀ (by norm_num)]
lemma prime_pow {F:Type*} [AddCommMonoid F] (U V:Name G→Name G→Name G→F)(h:∀ i j k,U i j k=V j k i): (∑ i:Name G,∑ j:Name G,∑ k:Name G,U i j k)=∑ i:Name G,∑ j:Name G,∑ k:Name G,V i j k:=by simp_rw [h]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
lemma breadth (x:Cover): b_1 W x= ∑ i:Name G,∑ j:Name G,∑ k:Name G,(3*fuel i j k) • (b_s W x i*b_r g W x j*b_r g W x k):=by
  let L:=b_r g W x; let R:= b_s W x; let f(i j k):=fuel i j k • (R i*L j*L k); let s:=∑ i,∑ j,∑ k,f i j k; have ht : (∑ i,∑ j,∑ k,(f i j k+ f j k i+ f k i j))=s+s+s:=by
    simp_rw [Finset.sum_add_distrib]; rw [← show s=∑ i,∑ j,∑ k,f j k i from (prime_pow _ _ (fun _ _ _=>rfl)).symm,← show s=∑ i,∑ j,∑ k,f k i j from prime_pow _ _ (fun _ _ _=>rfl)]; -- inspect rw
  rw [show b_1 W x=s+s+s from ?_]; swap
  · rw [← ht,b_1]; unfold B; simp_rw [map_sum,map_smul,map_mul,stimulated,map_mul,π0,π1, show plusV (G:=G)=spark (G:=G) true from rfl,translatedL g]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>?_ ; unfold f; rw [← turn_fuel i, turn_fuel k,← smul_add,← smul_add]; apply congr_arg; change (R i*L j+L i*R j)*L k+L i*L j*R k=_; ring
  unfold s; rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _=>?_ ; rw [mul_smul]; change f i j k + _ + _= (3:ℂ) • f i j k; module
lemma allowsB (x): Trace.volume x (Prelude.mark1 (W.surveys 6) (Bfield G)) - b_1 W x∈ DegZ (UnitIndex G) 3 :=upgraded A x (Bfield G) (n:=2) (hom_g b_rank)
lemma allowsU (x): Trace.volume x (Prelude.mark1 M (Ufield G))-u_1 W x∈ DegZ (UnitIndex G) 2:= upgraded M x (Ufield G) (n:=1) (hom_g u_rank)
end YM.XSpace.Chiral

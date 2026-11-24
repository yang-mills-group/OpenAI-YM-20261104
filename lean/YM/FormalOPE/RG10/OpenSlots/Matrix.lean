import YM.FormalOPE.RG10.OpenSlots.BankLayer
/-!
 # Partition of the normalized jacobian germ for an actual open step
 (here open means at the full non-tree next B in our bare prescription).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof Router
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S: StepData c f} {L: Fabric G c} {P:Inside S.ratio}
variable {H:S.patch.Branches S.kernel G} {hf:_root_.Even f.val}{t:S.Choices} {C:Cloth L}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Ω"=> Field (Cloth.choose T0)
local notation "F"=> Cross (G:=G) S P
local notation "B"=> Field C.choose
local notation "κ"=> exchange (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "π"=> spool (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Γ"=> layer S H t hf L
local notation "K"=> Index S P
local notation "Ψ"=> Atlas (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
lemma jacobi (J:ChartRatio G)(x y): jacobian J (d (x,y))= jacobian J x * jacobian J y:= by
 unfold jacobian; rw [←Equiv.prod_comp (e:=Ψ) (fun i=>(fee J ((d (x,y)) i))), Fintype.prod_sum_type]; simp only [fast_slot,tail_slot] -- e proof instance on Index
lemma jac_er (J:ChartRatio G): jacobian J (U:=((T0).choose.Bulk))= ((jacobian J ∘ LinearMap.fst ℝ F (Flats G c)) ∘ κ) * (jacobian J ∘ π):= by
 ext1 u; obtain ⟨⟨x,y⟩,rfl⟩:= (d).surjective u; rw [jacobi]; simp [trade,spinning]
variable {E Y K' : Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup K'][NormedSpace ℝ K']
lemma boost_c (a:Y→ₗ[ℝ] E)(p:ℝ): boost a (roll p)= roll p:= by apply into; intro x; simp only [caught,rollThrough]
lemma boosts (a:Y→ₗ[ℝ] E)(b:K'→ₗ[ℝ] Y)(p:Ticket E): boost b (boost a p)= boost (a ∘ₗ b) p:= by apply into; intro; simp [caught]
lemma leaned (a:Y→ₗ[ℝ] E)[FiniteDimensional ℝ Y]{b:E→ℝ}(h:ContDiffAt ℝ ω b 0): ContDiffAt ℝ ω (b ∘ a) 0:= (show ContDiffAt ℝ ω b (a 0) from by rw [map_zero]; exact h).comp 0 (LinearMap.toContinuousLinearMap a).contDiff.contDiffAt
lemma split_tissue {J:ChartRatio G}(hj:LocalRatio J): tissue J ((T0).choose.Bulk)= boost κ (boost (LinearMap.fst ℝ F (Flats G c)) (tissue J K)) * Ancestor (tissue J C.choose.Bulk) := by
 let R:=LinearMap.fst ℝ F (Flats G c); let μ:= R ∘ₗ κ
 unfold tissue; change roll (_⁻¹) * rise _= (boost _ (boost R _))* (boost π _)
 let a:= jacobian J (U:=K); let b:= jacobian J (U:=C.choose.Bulk)
 have ha:ContDiffAt ℝ ω a 0:= Ratio.jacobian_smooth hj
 have hb:ContDiffAt ℝ ω b 0:= Ratio.jacobian_smooth hj
 rw [boosts]; simp_rw [_root_.map_mul,boost_c,show jacobian J (U:=((T0).choose.Bulk))= (a ∘ μ) * (b ∘ π) from jac_er (C:=C) J, rise_mul ((leaned μ ha).of_le le_top) ((leaned π hb).of_le le_top)]
 simp_rw [Pi.mul_apply, Function.comp_apply,map_zero]
 change roll _ * _ = (roll _ * boost μ _ ) * (roll _ * boost π _)
 rw [Vault.climbing μ (ha.of_le le_top),Vault.climbing π (hb.of_le le_top),mul_inv]; unfold roll; simp_rw [map_mul]; ring
end YM.FormalOPE.RG10.OpenSlots

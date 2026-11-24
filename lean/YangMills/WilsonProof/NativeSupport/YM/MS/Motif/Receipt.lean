import YM.MS.Motif.Receipt
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Shift
/-!
# Bulk.M boot formulas `B` whose order-zero vanishes; partial orientation at all ℂ
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open Literal
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{n:ℕ}{z:ℂ}{F H:Mield G n}{B:T ( Mob G )}
local notation "S"=> field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product S
-- physically choose.Boot X ∀t.H+,H2, all other vanish. 
lemma Up0 (G:Gauge): pulseX G 0=0:= by simp [pulseX,hiss,χ]
-- maybe same note `S` collisions
lemma energetic (G:Gauge)(n:ℕ)(z:ℂ): core G n z= core G n 0 + z • top3 G n+ z^2 • top4 G n:= by
    have he (i j:Arts.L n): sume (G:=G) (cur z i j) (cur z i j)=sume (cur 0 i j) (cur 0 i j)+z • (sume (F₀ i j) (quill i j)+sume (quill i j) (F₀ i j))+ z^2 • sume (quill i j) (quill i j):= by
       unfold sume cur quill; simp only [ map_add,map_smul, LinearMap.add_apply,LinearMap.smul_apply,zero_smul,Pi.zero_apply, Pi.add_apply,Pi.smul_apply,add_zero,Finset.smul_sum, smul_add,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_; rw [smul_smul,pow_two]; abel
    unfold core top3 top4; simp_rw [he, Finset.sum_add_distrib,← Finset.smul_sum]; rw [smul_add,smul_add, smul_comm _ z]; rw [smul_comm _ (z^2)]; simp only [Finset.sum_add_distrib]
lemma zonal (i:Chan G n)(z:ℂ): applyS z G n i=applyS 0 G n i + z • blazeV G n i:= by
   rcases i with ⟨_|i,x⟩; · simp only [applyS,Sc, zero_smul, zero_div, neg_zero, Pi.smul_apply, blazeV,zero_add,smul_smul]; congr! 1; ring
   simp [applyS,blazeV,convoke]
lemma Class_at (G: Gauge)(z:ℂ): value (Mob G) z (χ G)= ploy G z- ploy G 0:= by
   rw [eq_sub_iff_add_eq]; simp only [χ,map_add,value_sl]; funext n; obtain hp:= energetic G n z; simp only [Pi.add_apply, B₁,B₂,Pi.smul_apply,pow_one,ploy,hp, smul_add]; unfold cape; simp_rw [ zonal _ z,map_add, Finset.smul_sum,smul_add,Finset.sum_add_distrib,map_smul]; -- only map_smul etc
   simp_rw [smul_comm z (phase _)]; abel
end YM.MS.Motif

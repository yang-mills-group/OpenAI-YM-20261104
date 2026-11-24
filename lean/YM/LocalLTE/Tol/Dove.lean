import YM.LocalLTE.Concert.Budget
import YM.Next.MULTISOURCE.Stencil
/-!
# Real calibrated cylinder supplies. Hold section stencils including cover placement. All LABEL directions in calibrated canonical finite requests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port.Sect
open Filter Function Set Lattice Wilson Labels Overlay Marker Source RG Finset Pressure MeasureTheory Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Animals FrameBox Grove Cabana
open Work.H03 Next.Foundations ConnectedActivityE6 Blaze Brush
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{d k:ℕ}
abbrev toes := localSection G d
set_option quotPrecheck false
local notation "L"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
private lemma toesK (S:Finset Cover): Finite (Source.Index G S):=by
   haveI : Finite (UsedEdges S):= Finite.of_injective (fun i : UsedEdges S => ((⟨i.val.1,i.property.1⟩:S),i.val.2)) (by rintro ⟨⟨a,b⟩,ha⟩ ⟨⟨c,d⟩,hc⟩ he; simp at he; aesop)
   unfold Source.Index; infer_instance
-- Map chart variables finite, at every Basis. Entire finite Cover known. no uniform budget yet for d.
variable (G d) (k) (i : ((Labels.frames G).level d).Index)
local notation "T"=> Source.Index G (L).stencil
local notation "F'"=> (L).stencil
-- compose projector.
def flora(x:T→G.Color) : ℂ:= MvPolynomial.aeval (fun j:T=> let y:= G.mat (G.lieExp (x j)) j.2.1 j.2.2.1
                                                            if j.2.2.2 then Star.star y else y) ((localSection G d).evalC (Extra.Histories.Size.axis F i)) -- indent
variable {n:Side}
-- no cross window.Wrap ZΦ. exact.
lemma aloof (i:Finset Cover): ∃ b:ℕ,∀ x∈i, x∈ Lattice.box b:=by
    classical
    choose g hg using fun x:Cover=> show ∃ b:ℕ,x∈ Lattice.box b from (by
         let b:=Finset.univ.sup (fun j=> (x j).natAbs)
         have h(j): (x j).natAbs ≤ b:= le_sup (f:= fun i => (x i).natAbs) (mem_univ j)
         refine ⟨b,mem_Icc.mpr ⟨fun i=> ?_,fun i=>?_⟩⟩ <;> ( have h:=h i; dsimp only; omega)) -- intro_vars remove
    refine ⟨i.sup g,fun x hx=>?_⟩; let k:=i.sup g; have hp:g x ≤ k:= le_sup hx; have hh:= mem_Icc.mp (hg x)
    exact mem_Icc.mpr ⟨fun j=> (neg_le_neg (Int.ofNat_le.mpr hp)).trans (hh.1 j),fun j=> (hh.2 j).trans (Int.ofNat_le.mpr hp)⟩ -- Box defeq? edit.
lemma insideL : ∃ b:ℕ,∀ (n:Side)(x:Site n), (L).footprint x⊆ neighbors b x:=by
    obtain ⟨b,hb⟩:= aloof ((L).stencil)
    refine ⟨b,fun n x i hi=> ?_⟩; obtain ⟨q,hq,rfl⟩:=mem_image.mp hi; exact (neighbors_mem ..).2 (Work.E08.separation_box_add x (hb _ hq)) -- order
-- Uniform global coupling-chart derivatives in fixed dimensions. Needed real unary.
open Extra.Histories
lemma authorityL (b:Bool) : ∃ x:ℝ, 0≤x∧ ∀ (n:Side)(o:Site n)(A:Directions G n), ‖A‖≤1→ Brush k x 1 (Port.scaleQ b ∘ (L).places (Size.axis F i) o ∘ FrameBox.Grove.soloV) A:=by
    haveI : Finite T:= toesK F'
    let _:= Fintype.ofFinite T -- install
    let X:= F' -- notation k captured
    let M(x:T→G.Color)(j:T): ℂ:= let y:= G.mat (G.lieExp (x j)) j.2.1 j.2.2.1 ; if j.2.2.2 then Star.star y else y
    have ht (j:T): ContDiff ℝ ω (fun x=> M x j):= by
       let C : (T→G.Color)→G.Mat:= fun x=> G.mat (G.lieExp (x j)); have hc : ContDiff ℝ ω C:= G.exp_jet.comp (contDiff_apply ℝ G.Color j); let S:G.Mat →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap { toFun x:=x j.2.1 j.2.2.1,map_add' _ _:=rfl,map_smul' _ _:=rfl }
       have hz:= S.contDiff.comp hc; by_cases he:j.2.2.2
       · have hf: (fun x=> M x j)=(fun x=> (starL' ℝ) (S (C x)) ):= by funext i; unfold M; rw [if_pos he]; rfl
         rw [hf]; exact (starL' ℝ).contDiff.comp hz
       have hf: (fun x=> M x j)=S ∘ C :=by funext i; unfold M; rw [if_neg he]; rfl
       rw [hf]; exact hz
    have hp(q:MvPolynomial T ℂ):ContDiff ℝ ω (fun y=>MvPolynomial.aeval (M y) q):=by
       induction q using MvPolynomial.induction_on with
       | C c => simp_rw [MvPolynomial.aeval_C]; exact contDiff_const
       | add p q ih ig=> simp only [map_add]; exact ih.add ig
       | mul_X p i ih=> simp only [map_mul,MvPolynomial.aeval_X]; exact ih.mul (ht i)
    let q:=Port.scaleQ b ∘ (flora G d i)
    have hq: ContDiff ℝ ω q:= (scaleQ b).contDiff.comp (hp _)
    let y:= Metric.closedBall (0:T→ G.Color) 1; letI := FiniteDimensional.proper ℝ (T→ G.Color)
    obtain ⟨e,h₀,hE⟩:= Brush.compact (f:=q) (k:=k) (isCompact_closedBall (0:T→ G.Color) 1) (fun z hz=> hq.contDiffAt.of_le (by simp))
    refine ⟨e,h₀.le,fun n o A h=>?_⟩; let c (i:T):= (wrap n i.1.val.1+o,i.1.val.2)
    let T': (Directions G n) →L[ℝ] (T→G.Color):= ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (c i))
    have hb: ‖T'‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by rw [one_mul];exact pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr (fun i=> norm_le_pi_norm x (c i)))
    have hz:= Brush.reading T' (hE _ (show T' A ∈ y from Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact (T'.le_opNorm A).trans ((mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (one_mul _|>.trans_le h))))) hb; rw [one_mul] at hz
    have hx:(Port.scaleQ b ∘ (L).places (Size.axis F i) o ∘ FrameBox.Grove.soloV)= q ∘ T':= rfl -- Bool if different? expand
    rw [hx]; exact hz
end YM.LocalLTE.Port.Sect

import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Tests
/-! # Enrollment to take the scale derivatives without a derivative price as input.
 Fix the test family first (e.g., using Gram, overdetermine here). Matrices use second
 argument reflected at partner on cap d; incoming independent. Left-multiplier to square.
 Formal products. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Sparks
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Read Comparing Pose Original Matrix Quotes
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d}
    (hJ:Leading U J) (P:Realized J Y N A (Paper.meter U J N.criterion))
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    (h : Shop U J N) (hp: normal U J N.store)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
abbrev Port (G : Gauge)(d:ℕ):= Test 2 × Toon G d
abbrev levy (a:Port G d) (u:Sec G d) : Tags G d 2:= ![u,prism (theory a.2)]
local notation "T" => Toon G d
def loadMatrix (A:Finset (Port G d)) : Matrix A (Toon G d) (PowerSeries ℂ) := fun i j => profile (storyV N (levy i.val (theory j))) i.val.1

def loadZero (j:T) (x : Points 2) : (T→ℂ)→ₗ[ℂ] ℂ := ∑ k:T, (fxt (V d) x 0 ![theory k,prism (theory j)]) • LinearMap.proj k
-- `∑` read vector coherence on columns
lemma agrees (j:T)(x:Points 2) (v:T→ℂ) : loadZero N j x v = ∑ k:T, fxt (V d) x 0 ![theory k,prism (theory j)] * v k := by simp only [loadZero,LinearMap.sum_apply]; rfl
variable (A':Finset (Port G d))(y:↥A') (a:Port G d)
def elder (a:Port G d) : (Toon G d→ℂ)→ₗ[ℂ] ℂ := ∑ i:T, constantCoeff (profile (storyV N (levy a (theory i))) a.1) • LinearMap.proj i
include H in
lemma vallder (v:Toon G d→ℂ) : elder N a v=a.1.applyTo (fun x=> loadZero N a.2 x v) := by
   have hc(j:T) : ContinuousOn (fun x=> fxt (V d) x 0 (levy a (theory j))) (conf 2) := by simpa only [story_charge] using (PT_cost N M H (levy a (theory j)) 0).continuousOn
   have he(j:T) : constantCoeff (profile (storyV N (levy a (theory j))) a.1) = a.1.applyTo (fun x=> fxt (V d) x 0 (levy a (theory j))) := by rw [← coeff_zero_eq_constantCoeff_apply, Sparks.profile, coeff_mk]; simp_rw [story_charge]
   -- assert explicit rewriting under no instance holes
   simp only [elder,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply, he]
   have hg (x:Points 2) : loadZero N a.2 x v = ∑ k : T, fxt (V d) x 0 (levy a (theory k)) * v k := agrees N a.2 x v
   simp_rw [hg, Test.applyTo,Finset.mul_sum]; rw [integral_finsetSum _ (fun i _=> a.1.smearing ((hc i).mul_const _)) ]; refine Finset.sum_congr rfl (fun i _=>?_); rw [smul_eq_mul,← integral_mul_const]; exact integral_congr_ae (Eventually.of_forall fun x=> mul_assoc ..)
lemma loaf (v:Toon G d→ℂ) : ((loadMatrix N A').map (constantCoeff (R:=ℂ))) *ᵥ v =
    fun i=> elder N i.val v := by
  funext x; unfold elder; rw [LinearMap.sum_apply]; rfl

-- use template from Normalize.Forecast.finalists
private lemma witnesses {E I:Type*}[AddCommGroup E][Module ℂ E][FiniteDimensional ℂ E](L:I→ E→ₗ[ℂ]ℂ):
    ∃ s : Finset I, ∀ x,(∀ i∈s,L i x=0) → ∀ i,L i x=0:=by
  let U (s:Finset I):= ⨅ i:s, LinearMap.ker (L i.val)
  have he : ∃ n:ℕ,∃ s,Module.finrank ℂ (U s)=n:= ⟨_,∅,rfl⟩
  obtain ⟨s,hs⟩:= Nat.find_spec he; refine ⟨s,fun x hx i=>?_⟩
  have hL: U (insert i s)≤ U s:=le_iInf fun k=> iInf_le_of_le (⟨k.1,Finset.mem_insert_of_mem k.2⟩:(insert i s: Finset I)) le_rfl
  have hu:= Submodule.eq_of_le_of_finrank_le hL (hs ▸ Nat.find_min' he (show ∃ t:Finset I,Module.finrank ℂ (U t)=Module.finrank ℂ (U (insert i s)) from ⟨_,rfl⟩))
  have hh:x∈ U (insert i s):= by rw [hu]; exact (Submodule.mem_iInf _).mpr fun j=> LinearMap.mem_ker.mpr (hx j.1 j.2)
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hh ⟨i,Finset.mem_insert_self ..⟩)
include H
lemma Gram_price (j:T)(v:Toon G d→ℂ) : loadZero N j paired_profile v=(GramP G d *ᵥ v) j:= by
  rw [agrees]; refine Finset.sum_congr rfl fun k _=>?_
  rw [fxt, dif_pos profile_space, ( H.separatedOPE 0 ).wilson.wardRank ]; congr 1
  change Wick.moment G paired_profile _=GramP G d j k; rw [GramP, paired_profile, O.Enh.RootG, O.Enh.lamp, Maxwell.Free.bond_eval]; apply congr_arg; ext1 i; fin_cases i <;> rfl

omit H
structure Spare (d:ℕ) where
   axis : Finset (Port G d)
   tally : Matrix (Toon G d) axis ℂ
   invert : tally * ((loadMatrix N axis).map (constantCoeff (R:=ℂ)))=1
include H
lemma enrollment (d:ℕ) : Nonempty (Spare N d) := by
   obtain ⟨S,h⟩:= witnesses (elder N (d:=d))
   let K:= (loadMatrix N S).map (constantCoeff (R:=ℂ)); let T₀:= LinearMap.toMatrix' K.mulVecLin.leftInverse
   have hr : LinearMap.ker K.mulVecLin = ⊥ := by
      rw [Matrix.ker_mulVecLin_eq_bot_iff]; intro v hv; rw [show K= _ from (rfl : K=(loadMatrix N S).map (constantCoeff (R:=ℂ))), loaf] at hv; have he:= h v (fun i hi=> congr_fun hv ⟨i,hi⟩)
      apply (Matrix.mulVec_injective_iff_isUnit.mpr (positive_unit (GramP_pos (G:=G) (d:=d)))); ext1 j
      have hx : ContinuousOn (fun x=>loadZero N j x v) (conf 2) := by
         simp_rw [agrees]; apply continuousOn_finsetSum; intro k _; apply ContinuousOn.mul_const
         simpa only [story_charge] using (PT_cost N M H (![theory k,prism (theory j)]) 0).continuousOn
      rw [ Matrix.mulVec_zero, ← Gram_price N M H ]; refine Test.weak_null hx|>.1 (fun i=>?_ ) profile_space; exact (vallder N M H (i,j) v).symm.trans (he _)
   have eq(v:(Toon G d)→ℂ): T₀ *ᵥ (K *ᵥ v)=v := by rw [LinearMap.toMatrix'_mulVec]; exact LinearMap.leftInverse_apply_of_inj hr v
   refine ⟨S,T₀,?_⟩; apply Matrix.toLin'.injective; apply LinearMap.ext; intro v; change ((T₀*K)*ᵥ v)= (1:Matrix (Toon G d) (Toon G d) ℂ) *ᵥ v; rw [ ← mulVec_mulVec, eq,one_mulVec ]
end YM.FVA2.GradedFar259.Sparks

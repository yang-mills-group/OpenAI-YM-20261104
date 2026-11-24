import YM.X.Grow.GaugeJet
/-!
# Color of slip and purchase of the CT. Only harness positivity through shell-sector. Also show star coefficient reality later via finite exact Wilson.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Grow
open Lattice Wilson Next.Rank Normal LiftMark MvPolynomial Function Filter MeasureTheory Metric
open Reed Source PertExtension LatticePT Labels Maxwell Maxwell.Free Heat
open Stems (Brush Curly loom snap)
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge} {d n m:ℕ}
local notation "u"=> Okay G
local notation "K"=> vapor G
local notation "B"=> Book G
local notation "J"=> Curly G
variable (a:G.El)
def signL : Module.End ℝ (Brush G):= LinearMap.pi fun i=> G.adjoint a ∘ₗ LinearMap.proj i
lemma sign_axis (X:TaylorTower G)(n:ℕ): valP n (stoic (shade a X) n)= signL a (valP n (stoic X n)):= by
   cases n with
   | zero => rw [stoic,stoic, map_zero,map_zero]
   | succ n=>
      let Y:=castFace a n (X n); have ht := equiv_curl a (X n)
      rw [stoic, stoic]; funext i; change gather (CellsInt.mapZ i.1+tip i.2) ((Maxwell.gaugeJet (castFace a n (X n))).val i.2) = G.adjoint a (gather _ ((gaugeJet (X n)).val i.2))
      rw [equiv_curl]; unfold gather; simp only [LinearMap.coe_mk,AddHom.coe_mk,map_sum, map_smul];rfl
lemma btw (p:Word G): Hue.Fixed (Vertex.normalized p.S p.H p.sound p.chosen p.axis):= by
    apply Hue.Fixed.heat; intro s x; simp only [Vertex.combination,map_sum,map_smul]; exact Finset.sum_congr rfl fun i _=> congr_arg _ ((Vertex.basis_fixed _ _ _ _ _) s x)
lemma mark_color (p:Word G)(A:Brush G): Stems.snap (signL a A) (looking p)=Stems.snap A (looking p):= by
   let f(t:RG.Slot):= Stems.v A t; have he(t):Stems.v (signL a A) t=G.adjoint a (f t):= by
       change Stems.curl _ _ _ _=G.adjoint a (Stems.curl _ _ _ _); unfold Stems.curl
       simp_rw [map_sub,map_add];rfl
   unfold looking; simp_rw [Stems.looms,he]; exact btw p a _
lemma pigmentLevel (p : WickPol G)(d:ℕ): level scaleW d (pigment a p)= pigment a (level scaleW d p):= by
   apply hom_commute; intro i; rw [pigment,aeval_X]; exact symbol_hom _ (fun i=>i+2)
omit a
variable {p : Curly G}
lemma pigment_surf (h:∀ (a:G.El) A, Stems.snap (signL a A) p=Stems.snap A p) (d:ℕ) (a:G.El): pigment a (lessJob (trumpet (Okay G) valP d p))= lessJob (trumpet (Okay G) valP d p):= by
     apply Maxwell.equalPol; intro A; rw [pigment_action]; simp_rw [shorter,tone,sign_axis,← map_sum,h a]
lemma pigment_branch (h:∀ (a:G.El) A, Stems.snap (signL a A) p=Stems.snap A p) (d) (a:G.El): pigment a (lessJob (bloom d p))= lessJob (bloom d p):= by
     let q:= trumpet (Okay G) valP d p; change pigment a (lessJob (level K d q))=lessJob (level K d q); rw [←hom_commute lessJob less_hom, ← pigmentLevel, show pigment a (lessJob q) = _ from pigment_surf h d a]
lemma twice_bloom (d:ℕ)(p:J): level K d (bloom d p)=bloom d p:= by
     let H:=trumpet (Okay G) valP d p; ext i; change coeff i (Rise.trim (Rise.trim H K d) K d)= coeff i (Rise.trim H K d); simp only [Rise.trim_coeff]; split_ifs<;> rfl
lemma pigment_touched (h:∀ (a:G.El) A, Stems.snap (signL a A) p=Stems.snap A p) (d):Unmixed d (bloom d p):= ⟨twice_bloom d p, pigment_branch h d⟩

lemma loomed_pure (p: Normal.poly (Atom G)) (d:ℕ): purely (bloom d (loom p)):= by
     let Q:=trumpet (Okay G) valP d (loom p); have h: localMap (E:=Okay G) (rightCur (G:=G)) Q= Q:= by
         apply probe_ext; intro A; rw [probe_map]; unfold Q; simp only [tone,Stems.looms]
         apply congr_arg (fun f:Atom G→ℂ=> aeval f p); funext i; apply congr_arg Complex.ofReal; let n:= i.1
         have ht (s : Brush G) : Stems.v s i.1 i.2= taste (signal_arc (Heat.Ray.address i)) s:= by rw [taste_eval, arc_flat]; exact congr_arg (fun q:G.Color=> q i.2) (curling ..).symm
         rw [ht,ht,map_sum,map_sum]; apply Finset.sum_congr rfl; intro k _; apply Eq.symm (sub_eq_zero.mp _); rw [← map_sub,poles]; exact horn (Submodule.subset_span (show _∈ Set.range signal_arc from ⟨_,rfl⟩)) _
     change localMap (E:=Okay G) rightCur (level _ d Q)=level _ d Q; rw [← local_trim,h]
lemma bloom_physical (p:Word G)(d): bloom d (looking p) ∈ physicalJet G d := (component ..).mpr ⟨pigment_touched (fun a=>mark_color a p) d, loomed_pure ..⟩
end YM.PositionX.Grow

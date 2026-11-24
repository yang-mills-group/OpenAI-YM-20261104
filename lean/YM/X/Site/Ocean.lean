import YM.X.Site.Pays
/-!
# Cost class for exterior directions. Physical units for regulator spacing, free sequence on ℕ. Probe readings include any fixed offset within fan origin, therefore local hypotheses hold also for any fixed displacement. Induces actual Taylor data (Fill).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Ocean
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric Asymptotics
open Reed Stems Hinge Braid Fielding Print
open scoped Topology BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {G:Gauge}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "H"=> Hair G
local notation "ε"=>epsilon q
structure Tide (q:ℕ+)(R:ℝ)(A:ℕ→ Brush G):Prop where
   kind : ClearK A
   amounts (k:ℕ)(f:Fan G)(hf:f∈Reed.grads G k): OnStreet (gate q R) (fun i=> epsilon q i^(k+1)) 0 (fun i z=> flatL (A i) (leadsL z f))
   later (k:ℕ)(f:Fan G)(hf:f∈Reed.grads G k)(x:E4)(hy:‖x‖ ≤ R)(z:Fielding.Walk)(hz:plot q z x): Released (fun i=> (epsilon q i^(k+1))⁻¹*flatL (A i) (leadsL (z i) f))
variable {R:ℝ}{f:Fan G}(p:Fielding.Walk){A B: ℕ→ Brush G}
lemma Tide.up (h:Tide q R A)(hw:Tide q R B): Tide q R (A+B):= by
    refine ⟨fun j z=> ?_,fun k f hf=> ?_,fun k f hf x hy z hz=> ?_⟩
    · filter_upwards [h.kind j z,hw.kind j z] with i hi hp; rw [Pi.add_apply,map_add,Pi.add_apply,hi,hp,zero_add]
    · simp_rw [Pi.add_apply, ←taste_eval,map_add,taste_eval]; simpa only [taste_eval] using! OnStreet.add (h.amounts k f hf) (hw.amounts k f hf) -- simplify?
    simp_rw [Pi.add_apply,←taste_eval,map_add,mul_add,taste_eval]; exact Released.add (h.later k f hf x hy z hz) (hw.later k f hf x hy z hz)
lemma Tide.zoom (h:Tide q R A)(a:ℝ): Tide q R (a • A):= by
    refine ⟨fun j z=> ?_,fun k f hf=> ?_,fun k f hf x hy z hz=>?_⟩
    · apply (h.kind j z).mono; intro i hi; rw [Pi.smul_apply,map_smul,Pi.smul_apply,hi,smul_zero]
    · obtain ⟨c,hc,he⟩:= h.amounts k f hf; refine ⟨‖a‖*c,by positivity,?_⟩; filter_upwards [he] with i hi z hz; rw [Pi.smul_apply, ← taste_eval,map_smul,norm_smul,mul_assoc,taste_eval]; gcongr; apply hi z hz
    simp_rw [Pi.smul_apply,←taste_eval,map_smul,taste_eval,mul_smul_comm]; exact (h.later k f hf x hy z hz).smul ⟨a,tendsto_const_nhds⟩
lemma Tide.empty : Tide q R (G:=G) (fun _=>0):= by refine ⟨fun j z=>?_,fun k f hf=>?_,fun k f hf x hy z hz=>?_⟩; exact Eventually.of_forall (fun i=> congr_fun (map_zero (orderK j)) z); simp_rw [←taste_eval,map_zero]; exact OnStreet.zero; simp_rw [←taste_eval,map_zero,mul_zero];exact Released.zero
lemma Tide.ap (h:Tide q R A)(k:ℕ): Bark (gate q R) (fun i=> ε i^(k+1)) k 0 A := by
    intro j l; let x(i:ℕ)(z:Cover):= jumped l (raising j (A i)) z
    let f (p:G.ColorIndex):= jetRow k l ((0,j),p); have he (i z)(p:G.ColorIndex):flatL (A i) (leadsL z (f p))=x i z p:= by unfold f; rw [jets_lead,jets_row,pointB]; exact congr_arg (fun t=> jumped l (raising j (A i)) t p) (add_zero _)
    choose c hc Hx using fun p:G.ColorIndex=> h.amounts k (f p) (grad_row _ _); refine ⟨∑ p,c p,Finset.sum_nonneg (fun p _=>hc p),?_⟩; filter_upwards [eventually_all.mpr Hx] with i hi z hz; change ‖x i z‖ ≤ _; rw [Finset.sum_mul]; nth_rw 1 [restore_tan (x i z)]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun p _=>?_ ; rw [norm_smul, show ‖tan p‖=1 from (EuclideanSpace.basisFun _ ℝ).orthonormal.1 _,mul_one, ← he]; exact hi p z hz -- name

include hq
lemma Tide.sends (hr:R≥0)(h:Tide q R A)(l:Fin k→Axis)(j:Axis): Released (fun i=>(ε i ^(k+1))⁻¹ • jumped l (raising j (A i)) 0):= by
    apply Released.pinj (WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).toLinearMap (WithLp.linearEquiv 2 ℝ _).injective -- name signature
    apply Released.piR; intro i; have he:= h.later k (jetRow k l ((0,j),i)) (grad_row _ _) 0 (by simpa using hr) _ (plot.constant hq (0:Cover)); simp_rw [leads_zero,jets_row] at he; exact he
end YM.PositionX.Ocean

import YM.WilsonCoeffUV.Marked.Step.TimeLog
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08
open scoped Topology BigOperators
variable {c f:Side}{ι U U':Type}{J I K S T:Finset ι}{D k:ι→ℕ}{i j e r h N m l:ℕ}{G:Gauge}{V:Type}

lemma Equation.mapKin {R R':Type}[CommRing R][CommRing R'][DecidableEq ι](p:R→+*R') {L M:Sac ι R}(h: Equation L M): Equation (p ∘ L) (p ∘ M):=by
    refine ⟨by rw [Function.comp_apply,h.1,map_one],by rw [Function.comp_apply,h.2.1,map_zero],?_⟩; funext S; have H:=congr_arg p (congr_fun h.2.2 S); unfold shells dial at *; simpa only [map_mul,map_sum,map_nsmul] using! H
lemma jamp {A:Case D} {P:Pal (Pen D S) U}(f:Matrix U U' ℝ)[Fintype U]: pPly A S (fun i=> Blue.fade f (P i))=fun i=>Blue.fade f (pPly A S P i):=funext fun i=>cloak_fade (touch A S).toLinearMap f (P i)
def finalZ {V U:Type}[NormedAddCommGroup V](P:Layers V U)(k:ℕ)(e:ℕ): Gen V U:=∑ i∈Finset.range (1+k+3*e),P i e
lemma zamp {A:Case D} (P:Layers (Pen D S) U)(k:ℕ): pPly A S (finalZ P k)= finallyA k (fun i=> pPly A S (P i)):=by funext e; change cloaks (touch A S).toLinearMap (finalZ P k e)=_; rw [finalZ,map_sum]; rfl

-- Step finite reference, fixed origins
section
variable [DecidableEq ι] (S:StepData c f)(Z:Forest S.ratio)(H:FaceRow)(M:Matrix (Body 1 f) (Body 1 c) ℝ)(Ñ: ChartRatio G) (P:PChart G f)(K: family G D)
abbrev AT:= extractV G S Z M
abbrev plank (r):=srCold ((levelsO K r).1 f) (extractV G S Z M)
abbrev oven (r):= srShade S Z H M Ñ P ((levelsO K r).1 f)
def inHeat:=turnTLog (oven S Z H M Ñ P K)
local notation "Hd" => H
local notation "s₁" => S
local notation "Fst"=> Z
omit [DecidableEq ι] in
lemma peelR {D}(W:Pal (Pen D I) (Woods G f))(A:Case D): (fun i=> pPly A I (srShade s₁ Fst H M Ñ P W i))=srShade S Z H M Ñ P (pPly A I W):=by
    let F:= extractV G S Z M; have ht:pPly A I (srCold W F)=srCold (pPly A I W) F := jamp _
    let G':= fillSlots (Woods G c) (covariance G S Z H); let D':=xray S Z H M Ñ P
    rw [srShade,srShade,← ht];
    funext i j; change cloaks (touch A _).toLinearMap (bul G' D' (srCold W F) i j)=_;  exact cloak_bul ..
lemma at_q (t: shellK 2 P)(b: LocalRatio Ñ)(p:Eu k K):∀ I,Lit (mass k I) (oven S Z H M Ñ P K I):=by
   intro I; exact ⟨srStops S Z H M _ t b ((placedO K p I).span _),srPure S Z H M Ñ P ((placedO K p I).pale _)⟩
lemma heatE (A:Case D)(t:shellK 2 P)(b:LocalRatio Ñ)(p:Eu k K) : Equation (fun J=> skyVal A (oven S Z Hd M Ñ P K J) (mass k J)) (fun J=> skyVal A (inHeat S Z Hd M Ñ P K J) (mass k J)):=by
   apply flashEra _ _ (at_q S Z Hd M Ñ P K t b p); unfold skyVal oven; rw [peelR,empty_level,pen_puff]
   let Q:= srShade S Z H M Ñ P (uband 1); let η:= fillSlots (Woods G c) (covariance G S Z H); let Y:= xray S Z H M Ñ P
   let R:= mass k ∅; have ht:stops R Q:= srStops S Z H M R t b (uband_length _ _ R)
   have hF: Q= bul η Y (uband 1):=by unfold Q srShade; rw [show srCold (uband 1) (extractV G S Z M)=uband 1 from funext fun i=> tilt_zero ..]
   apply lamp_ext; intro j i; rw [glance ht]; rw [hF,oxidize]; by_cases hv:j=0
   · subst j; rw [if_pos rfl,← coeff_mk i (fun v=> totalR (uband (U:=Joint G f c) 1 v))]; change coeff i (flash (uband 1))= _; rw [uband_flash,map_one]; simp only [coeff_one]; split <;> first | rw [map_zero] | rw [span_zero,map_one]
   rw [if_neg hv]; simp only [totalR,Pi.zero_apply,paint,map_zero,finsum_zero]; rw [span_time, coeff_one]; split
   · simp only [map_one,Polynomial.coeff_one]; rw [if_neg hv]
   simp
lemma coldE (t:shellK 2 P)(b:LocalRatio Ñ)(p: Eu k K)(v:K ∅=0)(I:Finset ι): inHeat S Z H M Ñ P K I 0=srCold ((K I).1 f) (extractV G S Z M):=by
   let T:=extractV G S Z M; let L:= inHeat S Z H M Ñ P K; let X:=oven S Z H M Ñ P K
   let Y I:= srCold ((K I).1 f) (extractV G S Z M)
   have hI:= at_q S Z H M Ñ P K t b p; have hq (I):=turn_stop X hI I
   funext i j x; apply pen_inj; intro A
   have hx:= (heatE S Z H M Ñ P K A t b p).mapKin (stopF (U:=Joint G f c) 0)
   let m₀:= loom (camber G T)
   let C I:= flash (pPly A I (L I 0)); let V I:= flash (pPly A I (Y I)); let W:= m₀ ∘ feeble (levelsO K) A f
   have hw I: m₀ (feeble K A f I)= V I:=by
       unfold feeble readO V; unfold Y srCold; rw [jamp]; exact loom_fade _ _ (finite_shell (ply_shell _ ((p _).span _)))
   have he:= (levels_exp K p v A f).mapKin m₀; rw [show (m₀ ∘ feeble K A f)= V from funext hw] at he
   have hX: Equation W C:=by
       convert! hx using 1
       · funext I; let U:= X I; let F:=pPly A I ((levelsO K I).1 f); rw [Function.comp_apply,skyVal,setV (under_pen U (hI I).stop A)]
         change m₀ (flash F)= flash (pPly A I (U 0)); rw [show U 0= plank S Z M (G:=G) K I from funext fun _=>bul_zero ..]; unfold plank srCold; rw [jamp]; exact loom_fade _ _ (finite_shell (ply_shell _ ((placedO K p I).span _)))
       · funext I; rw [Function.comp_apply,skyVal,setV (under_pen (L I) (hq I).stop A)]
   have hv : shellK (mass k I) (L I 0):=fun i j z=> (hq I).stop _ _ _ (by omega)
   have ht:= congr_fun (Equation.unique W C V hX he) I; have hf:= by_flash (ply_shell (touch A I).toLinearMap hv) (ply_shell (touch A I).toLinearMap (fade_shell _ ((p I).span _))) (fun i=> ply_pure _ ((hq I).shine_ 0 i)) (fun i=> ply_pure _ (fade_pure ((p I).pale _ i) _)) ht
   exact congr_fun (congr_fun (congr_fun hf i) j) x
end
end YM.WilsonCoeffUV.Wheel.Mark

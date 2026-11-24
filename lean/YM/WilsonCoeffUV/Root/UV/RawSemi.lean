import YM.WilsonCoeffUV.Root.UV.InverseTransfer
/-!
# Transport raw columns. Right affix after coupling substitution required!
Semantic justification via finite-port flash. No extra order (transport convolution). -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n f:Side}{U V:Type*}{r h D l e j k a N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}
lemma reedDear (S:StepData n f)(K:Forest S.ratio)(Ñ:ChartRatio G)(H:FaceRow) (M:Matrix (Body 1 f) (Body 1 n) ℝ)(p:PChart G f) (U:Pal ℝ (Woods G f))(k:ℕ)(A:Cost) (v:LocalRatio Ñ)(e:S.patch.Branches S.kernel G) (hs:(H.acts f).transpose=H.acts f)(hq:shellK k U)(hp:∀ i,Pure (U i))(he: shellK 2 p)(hb:∀ i,Pure (p i)): reed S K H M Ñ p k (affix A U) = affix A (reed S K H M Ñ p k U):=by
    let T:= reed S K H M Ñ p k U; let W:= inside S K H M Ñ p; let P:=affix A U; have he':∀ i,Pure (P i):= aspire A U hp
    let O:=reed S K H M Ñ p k P
    have ht: W*flash O=W*flash (affix A T):=by
       have hP:=affix_shell A _ hq; have hx:= inside_reed S K H M k he v hP e hs hb he'; have hv:=inside_reed S K H M k he v hq e hs hb hp
       have hh: insideMark S K H M Ñ p P= insideMark S K H M Ñ p U * soil A:= by
          have hz {U V:Type}[Fintype U][Fintype V](M:Matrix U V ℝ): loom M (soil A)=soil A:=by ext n; unfold loom soil cord; simp [MvPolynomial.algebraMap_eq]
          have hC {U V:Type}[Fintype U][Fintype V]: holdUp U (soil (U:=V) A) = soil A:= by ext n; unfold holdUp holdUpPoly soil; simp
          unfold insideMark P; rw [sponsor _ _ hq,map_mul,hz, mul_comm (soil A),← mul_assoc,← W_param]
          rw [hC]
       rw [← show _= W*flash O from hx,sponsor _ _ (reed_band S K H M k he v hq), hh,hv]; exact mul_right_comm _ _ _ |>.trans (by unfold W; rw [mul_assoc])
    have hf := ((PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [show constantCoeff W=1 from inside_mass S K H M v]; simp) : IsUnit W).mul_right_inj.mp ht)
    funext i; apply gen_inj (finite_shell (reed_band S K H M k he v (affix_shell A U hq)) _) (finite_shell (affix_shell A _ (reed_band S K H M k he v hq)) _) (reed_smooth S K H M k Ñ p he' i) (aspire A T (reed_smooth S K H M k Ñ p hp) i)
    simpa only [flash,coeff_mk] using congr_arg (coeff i) hf
lemma jotAffix (v:Volume D)(A:Cost)(Y:Pal (Vote D) U): jot v (affix A Y)=affix A (jot v Y):= by ext i r x; rw [jot_here]; unfold affix; simp_rw [Finset.sum_apply,Pi.smul_apply,_root_.sum_apply,_root_.smul_apply,jot_here]
lemma reedAcross (S:StepData n f)(K:Forest S.ratio)(Ñ:ChartRatio G)(H:FaceRow) (M:Matrix (Body 1 f) (Body 1 n) ℝ)(p:PChart G f)(U:Vell G f D)(k:ℕ)(A:Cost)(v:LocalRatio Ñ)(e:S.patch.Branches S.kernel G)(hs:(H.acts f).transpose=H.acts f)(hq:shellK k U)(hp:∀ i,Pure (U i))(he:shellK 2 p)(hb:∀ i,Pure (p i)): reed S K H M Ñ p k (affix A U)= affix A (reed S K H M Ñ p k U):=by
   ext i r x c
   have hh P : jot c (reed S K H M Ñ p k P)=reed S K H M Ñ p k (jot c P):= reed_maps S K H M _ (((ContinuousLinearMap.apply ℝ ℝ) c).toLinearMap)
   have hx := reedDear S K Ñ H M p (jot c U) k A v e hs (jot_length _ hq) (fun i=> jot_code (W:=U) c (hp i)) he hb
   rw [←jotAffix,←hh,←hh,←jotAffix] at hx; exact congr_fun (congr_fun (congr_fun hx i) r) x
lemma mixedAff {U:Type}[Fintype U](A B:Cost)(Y:Pal ℝ U)(p:shellK k Y)(h:∀ i,Pure (Y i)): Blue.mix A (affix B Y)= affix (Bank.reel A B) (Blue.mix A Y):=by
   let P:= Blue.mix A (affix B Y); let Q:= Blue.mix A Y; have hY:= mix_length (A:=A) p; have he : redo A (soil (U:=U) B)=soil (U:=U) (Bank.reel A B):=by
       let P:= (redo (U:=U) A).comp (soil (U:=U)); let Q:= (soil (U:=U)).comp (Bank.reel A)
       have h : P = Q := by
           have he:P PowerSeries.X=soil A*PowerSeries.X:=by simp [P,soil,redo_X]
           have ht:Q PowerSeries.X=P PowerSeries.X:=by unfold Q; rw [RingHom.comp_apply,reel_X,map_mul, he,soil, map_X]
           apply serial_ext (by rw [he,map_mul,constantCoeff_X,mul_zero]) _ ht.symm; intro i; unfold P Q; rw [RingHom.comp_apply,RingHom.comp_apply,reel_C]; rw [show soil (U:=U) (PowerSeries.C i)=realS i by rw [soil,map_C]; rfl,redo_base]
       exact DFunLike.congr_fun h B
   have hv : flash P=flash (affix (Bank.reel A B) Q):=by unfold P Q; rw [sponsor _ _ hY, ← redo_stern _ (affix_shell B _ p),← redo_stern _ p, sponsor _ _ p,map_mul,he]
   funext i; apply gen_inj (finite_shell (mix_length (A:=A) (affix_shell B _ p)) _) (finite_shell (affix_shell _ _ hY) _) (mix_pure (aspire B Y h) _) (aspire _ _ (mix_pure h) _); simpa only [flash,coeff_mk] using congr_arg (coeff i) hv
lemma mixAcross {U:Type}[Fintype U](A B:Cost)(Y:Pal (Vote D) U)(p:shellK k Y)(h:∀ i,Pure (Y i)): Blue.mix A (affix B Y)= affix (Bank.reel A B) (Blue.mix A Y):=by
   ext i r x c; have he (P:Pal (Vote D) U): jot c (Blue.mix A P)= Blue.mix A (jot c P):=by ext i r x; rw [jot_here]; simp_rw [Blue.mix,Finset.sum_apply, Pi.smul_apply,_root_.sum_apply, _root_.smul_apply,jot_here]
   have hh:= mixedAff A B (jot c Y) (jot_length _ p) (fun i=>jot_code (W:=Y) c (h i)); rw [←jotAffix,← he,← he, ←jotAffix] at hh; exact congr_fun (congr_fun (congr_fun hh i) r) x
end YM.WilsonCoeffUV.Cosmos

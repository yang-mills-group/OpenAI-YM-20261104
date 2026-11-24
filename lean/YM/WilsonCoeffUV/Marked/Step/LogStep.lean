import YM.WilsonCoeffUV.Marked.Step.Logos
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08
open scoped Topology BigOperators
variable {c f:Side}{ι U:Type}{J K I S T:Finset ι}{D k:ι→ℕ}{i j e r h N m l:ℕ}{G:Gauge}{V:Type}
variable [DecidableEq ι]
section
variable (S:StepData c f)(Z:Forest S.ratio)(H:FaceRow)(M:Matrix (Body 1 f) (Body 1 c) ℝ)(Ñ: ChartRatio G) (P:PChart G f)(K: family G D)
lemma outerS (t:shellK 2 P)(b:LocalRatio Ñ)(p:Eu k K)(hq:∀ i,Pure (P i))(x:S.patch.Branches S.kernel G)(i j:ℕ)(X:Finset ι):
       let V:= fillSlots (Woods G c) (covariance G S Z H); let Y:= inHeat S Z H M Ñ P K; let E:= xray S Z H M Ñ P
       Y X (i+1) j=((i+1:ℕ):ℝ)⁻¹ • (ripple V (Y X i j)+ravel V E (Y X) i j+ravel V.transpose E (Y X) i j+∑ J∈X.powerset, if v:J⊆ X then sewsV V v (Y J) (Y (X\J)) i j else 0):=by
    intro V Y E; let O:= oven S Z H M Ñ P K; have hv Q:= at_q S Z H M Ñ P K t b p Q; have ho h e r (v:r>2+e ∨ r+2*h>3*e): E h e r=0:= span_abr V (pack_band S t) (pack_zero S b) h e r v
    have he:Lit 2 E:=⟨fun h e r H=> ho _ _ _ (by omega), pure_abr V (pack_pure S b x hq)⟩
    refine touches V E Y (turn_stop O hv) he (fun A=>?_) i j X; let d:= ramp E 2
    apply logPDE V d _ _ (heatE S Z H M Ñ P K A t b p)
    intro S'; change brush none (skyVal A (O S') (mass k S'))= _
    let F:= levelsO K S'; let U:= srShade S Z H M Ñ P (pPly A S' (F.1 f)); let W:= pPly A S' (F.1 f); let X:= srCold W (extractV G S Z M); let D:= mass k S'; have ht:skyVal A (oven S Z H M Ñ P K S') D=ramp U D:= by unfold skyVal oven U; rw [peelR];
    rw [show skyVal A (O S') D=ramp U D from ht]
    have hx:= placedO K p S'; exact lamp_bul ho (fade_shell _ (ply_shell _ (hx.span f))) (fun i=> fade_pure (ply_pure _ (hx.pale f i)) _) he.shine_ V

-- finish by stopping time/mix *after* normalized ordinary. key identities retain full product exactly.
def mist (C:Cost)(k:ι→ℕ)(X): Parcelized (Pen D X) G c:= Blue.mix C (fun i=>fade plug (finalZ (inHeat S Z H M Ñ P K X) (mass k X) i))
abbrev unmark (C:Cost)(k:ι→ℕ)(X): Parcelized (Pen D X) G c:= Blue.mix C (reed S Z H M Ñ P (mass k X) ((levelsO K X).1 f))
lemma windZ {Y:Type}[NormedAddCommGroup Y] (X:Layers Y U)(p:stops i X): shellK i (finalZ X i):=by
    intro k r h; unfold finalZ; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun j _=> p _ _ _ (by omega)
lemma steaks (C:Cost)(t:shellK 2 P)(b:LocalRatio Ñ)(p:Eu k K)(X):
    let Y:= mist S Z H M Ñ P K C k X; shellK (mass k X) Y ∧∀ i,Pure (Y i):=by
    intro Y; have hv:= turn_stop (oven S Z H M Ñ P K) (at_q S Z H M Ñ P K t b p) X
    have h i:Pure (finalZ (inHeat S Z H M Ñ P K X) (mass k X) i):=by
        intro r; unfold finalZ; rw [Finset.sum_apply]; apply Blue.Smooth.sum; exact fun j _=> hv.shine_ j i r
    refine ⟨mix_length (fade_shell _ (windZ _ hv.stop)),mix_pure (fun i=> fade_pure (h i) _)⟩

omit [DecidableEq ι] in
lemma atomS {D}(V:Layers (Pen D I) (Joint G f c))(A:Case D)(C:Cost)(z:stops i V):
      redo C (loom plug (stopF 1 (skyVal A V i)))=flash (pPly A I (Blue.mix C (fun j=> fade (plug (U:=Woods G f) (V:=Woods G c)) (finalZ V i j)))):=by
    let F:= finalZ V i; have ht:= windZ V z
    rw [skyVal, at_one _ i (under_pen V z A)]; change redo C (loom plug (flash (finallyA i (fun j=> pPly A I (V j)))))=_; rw [← zamp V i, loom_fade plug (pPly A I F) (finite_shell (ply_shell _ ht)), ← jamp plug, redo_stern C (ply_shell _ (fade_shell _ ht)), ply_mixX]

lemma WindE (C:Cost)(A:Case D)(t:shellK 2 P)(b:LocalRatio Ñ)(p:Eu k K) : Equation (fun J=> flash (pPly A J (unmark S Z H M Ñ P K C k J))) (fun J=> flash (pPly A J (mist S Z H M Ñ P K C k J))):=by
   have ht X:= at_q S Z H M Ñ P K t b p X; have hx:= (heatE S Z H M Ñ P K A t b p).mapKin ((redo (U:= Woods G c) C).comp ((loom (plug (U:=Woods G f))).comp (stopF 1)))
   convert! hx using 1
   · funext J; exact (atomS (I:=J) (oven S Z H M Ñ P K J) A C (ht J).stop).symm
   funext J; exact (atomS (I:=J) (inHeat S Z H M Ñ P K J) A C (turn_stop (oven S Z H M Ñ P K) ht J).stop).symm
end

variable (A:Levels G)(Ñ:ChartRatio G)(m N:ℕ)(K:family G D)
def edV (k:ι→ℕ)(X):= verseI A Ñ m N (mass k X) (levelsO K X)
def logO (k:ι→ℕ): family G D:=reverseO (edV A Ñ m N K k)
lemma vol (k:ι→ℕ)(t:m<N)(v:G.Simple)(b:LocalRatio Ñ)(u:Eu k K): Eu k (edV A Ñ m N K k):=fun i=>Auth.verse A t v b (placedO K u i)
lemma edV_e (k:ι→ℕ)(t:m<N)(v:G.Simple)(b:LocalRatio Ñ): edV A Ñ m N K k ∅=puff D G:=by rw [edV,empty_level,puff_verse A t v b]
lemma logHush (k:ι→ℕ) : logO A Ñ m N K k ∅=0:= empty_reverse _
lemma step_L (k:ι→ℕ)(t:m<N)(v:G.Simple)(b:LocalRatio Ñ)(u:Eu k K): Eu k (logO A Ñ m N K k):=counted _ (vol A Ñ m N K k t v b u)
lemma step_S (k:ι→ℕ)(t:m<N)(v:G.Simple)(b:LocalRatio Ñ)(u:Eu k K): levelsO (logO A Ñ m N K k)=edV A Ñ m N K k:= wreathed _ (vol A Ñ m N K k t v b u) (edV_e A Ñ m N K k t v b)
lemma feeleg (k:ι→ℕ)(t:m<N)(v:G.Simple)(b:LocalRatio Ñ)(u:Eu k K)(n:Side)(I:Finset ι):
    (logO A Ñ m N K k I).1 n=mist (stepAt (ll A m) A.clock.kernel n) (xree (ll A m) A.clock.kernel n) (freeForms A N (m+1)) (roam A N m n) Ñ ((story A Ñ N (m+1)).1 (n*(ll A m).L)) K (ratioHigh A Ñ N m) k I:=by
   let H:=edV A Ñ m N K k; let Z:= logO A Ñ m N K k; let C:= ratioHigh A Ñ N m; let L:= ll A m; let P:= stepAt L A.clock.kernel n; let V:= xree L A.clock.kernel n; let M:=freeForms A N (m+1); let Q:=roam A N m n; let W:= (story A Ñ N (m+1)).1 (n*L.L); let Y:=mist P V M Q Ñ W K C k
   have ht:= vol A Ñ m N K k t v b u; have hv := step_L A Ñ m N K k t v b u I; have hp:= (old A Ñ v b N (m+1) t).basis (n*L.L); have hh:= steaks P V M Q Ñ W K C hp.lamp b u I
   funext i j x; apply pen_inj; intro B; have he:= Equation.unique (feeble H B n) (feeble Z B n) _ (levels_log H ht (edV_e A Ñ m N K k t v b) B n) (WindE P V M Q Ñ W K C B hp.lamp b u)
   have hr:=by_flash (ply_shell (touch B I).toLinearMap (hv.span n)) (ply_shell (touch B I).toLinearMap hh.1) (fun i=> ply_pure _ (hv.pale n i)) (fun i=> ply_pure _ (hh.2 i)) (congr_fun he I)
   exact congr_fun (congr_fun (congr_fun hr i) j) x
end YM.WilsonCoeffUV.Wheel.Mark

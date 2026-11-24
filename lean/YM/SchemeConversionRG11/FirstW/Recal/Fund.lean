import YM.SchemeConversionRG11.FirstW.Trice.Readout
import YM.SchemeConversionRG11.Read.Compose
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11 Complex Classical
open SchemeConversionRG11.FirstMS SchemeConversionRG11 Bridge
open scoped Topology ContDiff BigOperators Classical Matrix
variable {G:Gauge}{F: Labels.Frames G}{L:Side}{m d:ℕ}
lemma paidUp (hh:1<L.val) (hg:G.Simple) (Z:ℕ→Pack F) (H:∀ Q:Wash,stampB F Z (itinerary L hh) Q): Tendsto (transcribed F L (basic F) Z profileChoice) atTop (𝓝 (cTest G)) := by
 change Tendsto _ _ (𝓝 (∫ x:Points 3, (profileChoice:Points 3→ℂ) x * (↑(fullTransfer G x):ℂ)))
 apply archived hh Z (basic F) profileChoice profileChoice.hasCompactSupport profileChoice.continuous profileChoice.tsupport_subset
 intro σ hs z hz o ht
 have he:= scene hh hz hs o ht
 obtain ⟨R,ρ,B⟩:= Triad.shelter hz
 exact financed F hg he (Z∘σ) B (c:=fun i=>Rig.denom L (σ i)) (fun i=>Rig.exchangePt L (σ i)) (fun Q=> covers_sub F Z σ hs Q (H Q))
open Series Issue Tape
-- explicit regulator-indexed packs. normalizes d=6; lower via menu coherence.
def sap (F:Labels.Frames G)(L:Side)(Z:ℕ→Pack F)(i:ℕ): Series (Buffer F 6):= fun j=> if j=1 then -carryR (Full.period L i) (Full.topSpacing L i) (Z i) else 0
lemma sap₀ (Z:ℕ→Pack F) (L:Side)(i): sap F L Z i 0=0:= if_neg (by decide)
def FirstSap (F:Labels.Frames G)(L:Side)(Z:ℕ→Pack F)(i:ℕ): Issue F 6:= imprint (sap F L Z i) (bareSide L i)
lemma bareZ (h:1<L.val)(f:Test m)(v:Fin m→E F d): Tendsto (fun i=>bareSide (F:=F) (d:=d) L i m f 0 v) atTop (𝓝 (Issue.gaussian F d f v)) := by
 exact Rig.zerothProfile d F L h v f f.continuous f.hasCompactSupport f.tsupport_subset
lemma first0 (F:Labels.Frames G)(L: Side)(Z:ℕ→ Pack F)(i:ℕ)(f: Test m): FirstSap F L Z i m f 0 = bareSide L i m f 0:= by unfold FirstSap imprint hinge; rw [liftJet_zero]; change put (sap F L Z i 0) _ = _; rw [sap₀,put_zero];rfl
lemma first1 (Z:ℕ→Pack F)(i:ℕ)(L:Side)(f:Test m)(v:Fin m→E F 6): FirstSap F L Z i m f 1 v= transcribed F L v Z f i:=by
 unfold FirstSap imprint; rw [Tape.leading _ _ (sap₀ ..)]; simp only [add_apply, Tape.vary_at]; let A:= carryR (Full.period L i) (Full.topSpacing L i) (Z i)
 have hx(j: Fin m): bareSide (F:=F) (d:=6) L i m f 0 (update v j ((sap F L Z i 1).val (v j))) = -(bareSide (d:=6) (F:=F) L i m f 0 (update v j (A.val (v j)))):= by
    rw [show (sap F L Z i 1).val (v j)= -(A.val (v j)) from rfl]; let f:= bareSide (F:=F) (d:=6) L i m f 0; exact f.toMultilinearMap.map_update_neg v j _
 simp_rw [hx,Finset.sum_neg_distrib]; rw [add_comm, ← sub_eq_add_neg]; rfl
lemma tissue {A:ℕ→Tape F d m ℂ}(h:∀ v,Helen (fun i=> A i v)): Helen A := by
 let b:=Module.finBasis ℝ (E F d)
 let I:= Fin m → Fin (Module.finrank ℝ (E F d))
 let t(i:I):Fin m→ E F d:= fun j=> b (i j)
 let R:Tape F d m ℂ→ₗ[ℝ] (I→ℂ):= LinearMap.pi (fun i=> (ContinuousMultilinearMap.apply ℝ (fun _:Fin m=> E F d) ℂ (t i)).toLinearMap)
 have he: Injective R:=by
    intro u v hu; apply ContinuousMultilinearMap.ext; intro p
    have hv(f:Tape F d m ℂ): f p= ∑ z:I,(∏ j, b.coord (z j) (p j)) • (R f z):=by
       conv_lhs=> rw [← funext fun j=> b.sum_equivFun (p j)]
       rw [ContinuousMultilinearMap.map_sum_finset, Fintype.piFinset_univ]; apply Finset.sum_congr rfl; intro i _; exact f.map_smul_univ ..
    rw [hv,hv,hu]
 obtain ⟨g,hg⟩:= LinearMap.exists_leftInverse_of_injective (K:=ℝ) (V:=Tape F d m ℂ) (V':=I→ℂ) R (LinearMap.ker_eq_bot.mpr he)
 choose p hp using h; have hv: Tendsto (fun j=>R (A j)) atTop (𝓝 (p ∘ t)):= tendsto_pi_nhds.mpr (fun i=> hp _)
 have H : Continuous g:= LinearMap.continuous_of_finiteDimensional (𝕜:=ℝ) (E:=I→ℂ) (F':=Tape F d m ℂ) g
 have ht:=H.continuousAt.tendsto.comp hv; exact ⟨_, ht.congr fun i=> (show g _= _ from LinearMap.congr_fun hg (A i))⟩
lemma walkFirst (h:1<L.val)(p:Test m): Tendsto (fun i=> bareSide (F:=F) (d:=d) L i m p 0) atTop (𝓝 (gaussian F d p)):=by
 obtain ⟨X,H⟩:= tissue (F:=F) (d:=d) (A:= fun i=> bareSide L i m p 0) (fun v=> ⟨_,bareZ h p v⟩)
 have he: X = gaussian F d p := ContinuousMultilinearMap.ext (fun v=> tendsto_nhds_unique (show Tendsto (fun i=> bareSide (F:=F) (d:=d) L i m p 0 v) atTop _ from ContinuousAt.tendsto (ContinuousLinearMap.continuous (ContinuousMultilinearMap.apply ℝ _ ℂ v)|>.continuousAt (x:=X)) |>.comp H) (bareZ h p v))
 rw [he] at H; exact H
lemma goes (hg:G.Simple)(F: Labels.Frames G)(hh:1<L.val) (Z:ℕ→Pack F)(hz:∀ Q:Wash,stampB F Z (itinerary L hh) Q) : ∃ M: Issue F 6, M.Twist ∧ M 3 profileChoice 1 (basic F)=cTest G ∧ Limits 1 atTop (FirstSap F L Z) M:=by
 have HP(m:ℕ)(p:Test m): Helen (fun i=> FirstSap F L Z i m p 1):= by
    apply tissue; intro v
    obtain ⟨W,H⟩:= reflex hh hg Z v hz
    refine ⟨_,(archived hh Z v p p.hasCompactSupport p.continuous p.tsupport_subset H).congr fun i=>?_⟩; rw [first1]
 choose A h using HP; let M: Issue F 6:= fun i t j=> if j=1 then A i t else gaussian F 6 t
 refine ⟨M,fun _ _=>rfl,?_,?_⟩
 · have hx:=paidUp hh hg Z hz; change A 3 profileChoice (basic F)=_; have H:= (h _ profileChoice)
   let R := ContinuousMultilinearMap.apply ℝ (fun _ :Fin 3=> E F 6) ℂ (basic F)
   apply tendsto_nhds_unique (b:=cTest G) (R.continuous.continuousAt (x:=A 3 profileChoice) |>.tendsto.comp H); exact hx.congr fun i=> (first1 ..).symm
 intro i t j hj; interval_cases j
 · change Tendsto (fun i'=> FirstSap F L Z i' _ _ 0) _ (𝓝 (gaussian F 6 t)); simp_rw [first0]; exact walkFirst hh t
 exact h i t
end YM.RG11.FirstW

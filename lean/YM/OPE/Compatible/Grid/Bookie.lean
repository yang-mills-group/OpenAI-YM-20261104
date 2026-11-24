import YM.OPE.Compatible.Grid.Work
/-!
# spirit Difference loop at grade 0
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Page Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics PertExtension Series
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s b U D:ℝ}{d r m k q:ℕ}
variable {p:Script (Shade G) k}
-- intake leading
abbrev candor (v:fieldX (Shade G)):fieldX G.ColorIndex:= fun j=>(-bandC v j.1) j.2
def risingO (v:fieldX (Shade G)):= v + mountain (candor v)
lemma scan (p:Page (Shade G) k)(v:fieldX (Shade G)): Tendsto (fun t:ℝ=> (t^k)⁻¹ • (verseX (ships p) (lotU (t • v)))) (𝓝[>] (0:ℝ)) (𝓝 (wordX (fun _=> risingO v) p)):=by
     let f(t:ℝ):= board (lotU (t • v)); have he(i:Cover× Shade G): Tendsto (fun t:ℝ=> t⁻¹*f t i) (𝓝[>] (0:ℝ)) (𝓝 (risingO v i)):= by
           have hv := (arcRead v i); rw [hasDerivAt_iff_tendsto_slope] at hv; apply (hv.mono_left (show 𝓝[>](0:ℝ) ≤ _ from nhdsWithin_mono _ (by simp))).congr'; filter_upwards with t; rw [slope_def_module, taPZ_board v i]; simp [f] -- lemma
     apply (tendsto_finsetProd univ (fun i _=>he (p i))).congr'; filter_upwards with t; rw [← issue]; simp only [prod_mul_distrib, wordX, prod_const,card_univ,Fintype.card_fin,inv_pow,smul_eq_mul];rfl
where taPZ_board (v:fieldX (Shade G))(i:Cover × Shade G): board (lotU ((0:ℝ) • v)) i=0:=by unfold board; rw [taPZ,Gauge.curvature_unit];rfl
lemma sifts (p:Page (Shade G) k)(v:fieldX (Shade G)): wholeX (coff (ships p) k) (fun _=>v)= wordX (fun _=>risingO v) p:=by
     rw [← coinShots]; exact WardBin.leading_of_lim ((cash_smooth _ _).contDiffAt.of_le le_top) _ (scan p v)
lemma sifts_nil (p:Page (Shade G) k)(v:fieldX (Shade G))(h:r<k): wholeX (coff (ships p) r) (fun _=>v)=0:=by rw [←coinShots]; exact WardBin.leading_of_lim ((cash_smooth _ _).contDiffAt.of_le le_top) _ (WardBin.falls h (scan p v))
lemma normPost' (v:fieldX (Shade G))(h:Quiet v 0): Quiet (candor v) 1:=by
     obtain ⟨C,hc,H⟩:=staffQ _ h
     have he (x:Cover) (w:Walk) : ‖(pieces v x w).sum‖ ≤ C*w.length:=by
          induction w generalizing x with
          | nil=>simp [pieces]
          | cons i w ih=>
            have ht : ‖if i.neg then -indexS (i.used x) v else indexS (i.used x) v‖≤C:=by split; rw [norm_neg]; exact H _; exact H _
            unfold pieces; rw [List.sum_cons]; exact ((norm_add_le ..).trans (add_le_add ht (ih _))).trans_eq (by rw [List.length_cons,Nat.cast_add,Nat.cast_one]; ring)
     refine ⟨C,hc,fun i=>?_⟩; apply (PiLp.norm_apply_le ((-bandC v i.1):G.Color) _).trans; rw [norm_neg]; apply (he 0 (carryP i.1)).trans; rw [carryP, Stationary.route_length,sub_zero]; unfold poise notch; rw [pow_one]; gcongr; omega
lemma heather {w:fieldX G.ColorIndex}(hp:Quiet w r): Quiet (mountain w) r:=by
     obtain ⟨C,hc,H⟩:=hp; refine ⟨C * 2^r+C,by positivity,fun p=>?_⟩; rw [mountain]; apply (norm_sub_le ..).trans; rw [add_mul,mul_assoc]; exact add_le_add ((H _).trans (mul_le_mul_of_nonneg_left (ascentStep ..) hc)) (H _)
lemma quietSlide (h:p.abides)(hp: soot q p b)(hk:k*r≤q){v:Fin k→ fieldX (Shade G)}(w:Fin k→fieldX G.ColorIndex)(hu:∀ i,Quiet (v i) r)(hv:∀ i,Quiet (w i) r): wholeX p (fun i=> v i+mountain (w i))=wholeX p v:=by
     let f (s :Finset (Fin k))(i):=if i∈s then v i+mountain (w i) else v i
     let K(i:Fin k):= r; have hg : (∑ i,K i)≤q:=by simpa only [K,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.cast_id] using hk
     have ht(s' :Finset (Fin k)) : Glob (f s') K:=fun i=>by unfold f; split; exact quietAdd (hu i) (heather (hv i)); exact hu i
     have hy(s' :Finset (Fin k)): wholeX p (f s')=wholeX p v:=by
          induction s' using Finset.induction_on with
          | empty=>simp [f]
          | insert i s hx ih=>
               let w':= update (f s) i (mountain (w i)); have hu: wholeX p w'=0:=crest_zero p h hp (f s) i (w i) K hg (fun j _=> ht s j) (hv i)
               have hh: Glob w' K:=fun j=>by by_cases he:j=i; subst j; rw [show w' i= _ from update_self ..]; exact heather (hv i); rw [show w' j=f s j from update_of_ne he ..]; exact ht s j
               rw [choir i hp (ht s) hh hg (show f (insert i s) i=f s i+w' i from by simp [hx,w',f]) (fun j hj=>by simp [hj,f,w']),hu,ih,add_zero]
     simpa only [f,Finset.mem_univ,if_true] using hy univ
lemma frameO (h:p.abides)(hs:p.sorted)(hp: soot q p b)(he:2*k≤q): timbre ships p k=p:=by
     refine home (sootS ((paySpray G 0 q k k (by omega)).choose_spec.2 p b hp|>.1)) (sootS hp) (timbreT _ _ _) hs (φ:=atTop) epochX (tendsto_add_atTop_nat 1) (Eventually.of_forall fun i x=>?_)
     let u:=upl (0:Site (epochX i)) x; have hz:Quiet u 0:=⟨‖x‖,norm_nonneg _,fun j=>(norm_le_pi_norm x (0+wrap _ j.1,j.2)).trans_eq (by unfold poise;ring)⟩
     have hb:= (doReads hp he (fun _=>u) (fun _=> hz)).tsum_eq; change wholeX _ (fun _=>u)=wholeX _ (fun _=> u); rw [← hb]; simp_rw [sifts]; exact quietSlide h hp (show k*1≤q from by omega) (fun _=>candor u) (fun _=> quiet_up hz (Nat.zero_le _)) (fun _=>normPost' _ hz)
end YM.OPE.Flume.Script

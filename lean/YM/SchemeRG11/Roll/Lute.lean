import YM.SchemeRG11.Roll.Orbit
/-! Covariance at both seam and kernel, true multi field leg. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Patho
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long Air North Wolt Sew Dock MvPolynomial Bark Bare
open scoped Classical Pointwise ContDiff Matrix.Norms.Frobenius
variable {A:Type*}[AddCommGroup A][One A]{G:Gauge} {m n:ℕ}{N:Side} (s:Signed)(h:ℝ)
def atlas (i:Key G): Stem (Key G) ℝ:= ∑ j:Fin (Labels.dim G i.1), Finsupp.single ⟨i.1,j⟩ ((axes G i.1).coord i.2 (Taylor.turn s⁻¹.ortho (axes G i.1 j)))
def title (p:pLabel G):pLabel G:=vary (atlas s) p
lemma tinting (X: Labels.Jet G)(i:Key G): sense (rune X) (atlas s i)= rune (changedJet (fun _=>Taylor.turn s⁻¹.ortho) X) i:=by
 rw [atlas,map_sum]; simp only [sense,Finsupp.linearCombination_single]; conv_rhs=> unfold rune changedJet; rw [←(axes G i.1).sum_repr (X i.1)]
 rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul,map_smul]; exact mul_comm ..
lemma enrole(p:pLabel G): realCast (title s p)=Labels.rotated s.ortho (realCast p):=by
 apply eval_ext; intro A; rw [← Outlook.cabin,rotated,eval_changed, ←Outlook.cabin]; congr 1; unfold nib title; rw [varyV]; simp_rw [tinting]; rw [← show s⁻¹.ortho=s.ortho⁻¹ from map_inv Signed.inclusionO s]
lemma league(P:Paper (Code G A) ℝ)(v:trunk G A): aeval (cant v) (vary (scent s) P)= aeval (cant (wideLink G s v)) P:=by rw [varyV]; simp_rw [scent_p]
-- scale directly instead of commuting jet scale
lemma turf (p:pLabel G): vary (scent s) (stemZero h p)=stemZero h (title s p):=by
 apply viewers; intro A; rw [league, varyV,varyV]
 let J:Labels.Jet G:=fun i=> starJet false h (0:Cover) i A A
 have he (i:Key G)(v:trunk G ℤ):sense (cant v) (leafProbe h i)= (axes G i.1).coord i.2 (starJet false h (0:Cover) i.1 v v):=by rw [leafProbe,map_smul, alpha_at]; conv_rhs => rw [coins,map_smul]
 rw [title,varyV]; rw [show (fun i:Key G=>sense (cant A) (leafProbe h i))=rune J from funext (fun i=> he i A)]
 simp_rw [tinting]
 apply congrArg (fun x:Key G→ℝ=> aeval x p); funext i; rw [he i]; simp only [rotates,affine,Signed.act_zero,add_zero]; unfold rune J changedJet; simp only
lemma talem : (Atoll.unmarked G h).pull (atlas s)=Atoll.unmarked G h:=by
 let D:= Atoll.land G; let L:=Atoll.unmarked G h
 apply Dose.strict; intro i j
 have he:D.avg (vary (scent s) (stemZero h (X i*X j)))= D.avg (stemZero h (X i*X j)) :=by rw [Dose.colour,backer]
 rw [turf] at he; unfold title at he; simp only [stemZero,Dose.colour] at he
 have ht(b:Dose (Key G) ℝ)(i j:Key G):b.avg (X i*X j)=b.pulse i j:=by rw [Dose.release,vent,mkDerivation_X,Haze.Dose.avg_def,Haze.Dose.heat_C,aeval_C,b.beats i j];rfl
 exact (ht _ i j).symm.trans (he.trans (ht _ i j))
lemma pad0 (p:pLabel G): vary (scent s) (castZero h p)=castZero h (title s p):=by unfold castZero; rw [turf]; unfold title; rw [Haze.Dose.night,talem]
lemma expansion (p:pLabel G): vary (scent s) (expandW 1 p)= expandW 1 (title s p):=by
 apply viewers; intro A; rw [league]; have he:=resonate (title s p) A
 apply HasDerivAt.unique _ he
 let q:trunk G ℤ:=wideLink G s A; have h(t:ℝ): nib (soul A + t • (fun i=> (1/2:ℝ) • starJet true 1 (0:Cover) i A A)) (title s p) = nib (soul q + t • (fun i=> (1/2:ℝ) • starJet true 1 (0:Cover) i q q)) p:=by
     let f:= soul A+t • (fun i=> (1/2:ℝ) • starJet true 1 (0:Cover) i A A)
     unfold nib title; rw [varyV]; congr 1
     ext i; rw [aeval_X,aeval_X,tinting]; unfold rune q soul changedJet; simp only [Pi.add_apply,Pi.smul_apply,_root_.map_add,map_smul,rotates, affine,Signed.act_zero,add_zero]; rw [← secular 1 _ _ ((wideLink G s) A) ((wideLink G s) A), rotates]; simp only [affine,Signed.act_zero,add_zero]; rw [secular]
 simp_rw [h]; exact resonate p q
lemma climb (p:pLabel G): vary (atlas s) (etude h p)=etude h (title s p):=by
 apply run_inj; intro X
 unfold nib etude title; simp_rw [varyV]; congr 1
 ext i; rw [aeval_X,aeval_X]; simp [scaleStem,atlas,sense,Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=>mul_left_comm .. 
lemma pad1 (p:pLabel G): vary (scent s) (castFirst h p)=castFirst h (title s p):=by
 unfold castFirst; rw [← (expand_sc h _).1, expansion]; unfold title; rw [Dose.night,talem]; change expandW 1 _= _
 rw [← (expand_sc h _).1, climb];rfl -- shapes
lemma advance(o:Site N)(p:vellum G): vary (scent s) (adsorb o p)=adsorb (s.act o) (vary (scent s) p):=by
 apply viewers; intro A; rw [league, readAd,readAd,league]; rw [show absorb o ((wideLink G s) A)= (wideLink G s) (absorb (s.act o) A) from ?_]
 -- equiv
 funext e; unfold absorb; rw [wideLink_apply,wideLink_apply]; apply congrArg; apply congrArg A; cases h:((Lattice.posDir e.2).rotate s).neg <;> simp [Lattice.Step.used,h,←wrap_signed]; abel
end YM.SchemeRG11.Patho

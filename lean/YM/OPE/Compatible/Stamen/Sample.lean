import YM.OPE.Compatible.Fathom.Cook
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
abbrev Root (I:Type):= Cover×I
def toque (p:Script I (r+1))(a:Root I): Script I r:=fun u=> p (Fin.cons a u)
def usher (a:Root I) (i:ℕ): Page I i→Page I (i+1):= fun v => Fin.cons a v
lemma usher_inj (a:Root I): Injective (usher a i):=fun ⦃p q⦄ h=> funext (fun i=> by simpa only[usher,Fin.cons_succ] using DFunLike_congr h i.succ)
where DFunLike_congr {α β:Type} {f g:α → β}(he:f=g)(i:α): f i=g i:=congr_fun he i
lemma usherPrice (a:Root I)(u:Page I i): figure m u≤figure m (usher a _ u):=by
      have hp: stamp u≤stamp (usher a _ u):=by rw [perimeter,perimeter]; unfold usher; rw [Fin.sum_univ_succ]; simp -- goals
      unfold figure poise; gcongr
lemma owns (p:Script I (r+1))(a:Root I)(h:soot m p C): soot m (toque p a) C:=by
      let f(i:Page I (r+1)):= figure m i*‖p i‖; let g:= usher a r; let z(i:Page I r):=figure m i*‖toque p a i‖; have hp(i):0≤z i:=mul_nonneg (zero_le_one.trans (payer m i)) (norm_nonneg _); have hg(i): z i≤(f∘g) i:=mul_le_mul_of_nonneg_right (usherPrice a i) (norm_nonneg _)
      have hh:Summable (f∘g):=h.2.1.comp_injective (usher_inj a); have he:Summable z:=Summable.of_nonneg_of_le hp hg hh; refine ⟨hp,he,(he.tsum_le_tsum hg hh).trans ?_⟩; refine le_trans ?_ h.2.2; -- find
      exact (hh.tsum_le_tsum_of_inj g (usher_inj a) (fun i _=>h.1 i) (fun _=>le_rfl) h.2.1)
-- symmetry & Ward. actual δ calculation
lemma touchS (a:Root I)(p:Script I (r+1))(h:p.sorted): (toque p a).sorted:=by
      let A:= p; intro i; let s:=Equiv.Perm.decomposeFin.symm ((0:Fin (r+1)),i); funext v; rw [show swing i _ v=p (Fin.cons a v ∘ s) from ?_]; exact congr_fun (h s) (Fin.cons a v)
      apply congr_arg p; funext j; refine Fin.cases ?_ (fun j=>?_) j<;>simp [s,Equiv.Perm.decomposeFin_symm_apply_succ]
abbrev delta (a:Root I):fieldX I:= Pi.single a 1
lemma sola (p:Script I (r+1))(a:Root I)(z:Fin r→fieldX I): wholeX (toque p a) z=wholeX p (Fin.cons (delta a) z):=by
      let f(v:Page I (r+1)):=p v*wordX (Fin.cons (delta a) z) v; have hp(v:Page I r):p (usher a r v)*wordX z v=f (usher a _ v):=by simp [f,wordX,usher,delta,Fin.prod_univ_succ]
      change (∑' v,p (usher a _ v)*_)=∑' i,f i; simp_rw [hp]; apply Function.Injective.tsum_eq (usher_inj a); intro i hi; have ht:i 0=a:=by
           by_contra hc; apply hi; simp only [f,wordX,Fin.prod_univ_succ,delta]; simp [hc]
      exact ⟨Fin.tail i, by unfold usher; rw [← ht,Fin.cons_self_tail]⟩
variable [Fintype I]
omit [Fintype I] in lemma quieti (x:fieldX I)(w:ℝ) (h:∀ i,‖x i‖≤ w) (hp:0≤w): Quiet x 0:=⟨w,hp,fun i=>by unfold poise; rw [pow_zero,mul_one]; exact h i⟩
omit [Fintype I] in lemma quietX (a:Root I): Quiet (delta a) 0:=quieti _ 1 (fun i=>by by_cases h:i=a<;>simp [delta,h]) zero_le_one
lemma quietZ {n:Side}(w:deck I n): Quiet (unfoldX w) 0:= quieti _ ‖w‖ (fun _=> norm_le_pi_norm w _) (norm_nonneg _)
lemma veilX (p:Script (Palette I) (r+1))(h:soot m p C)(hp:p.abides)(a:Root (Palette I)):(toque p a).abides:=by
     intro i n w y; let X:= update w i (cliff y); rw [bridgeX, sola]; let f: Fin (r+1)→fieldX (Palette I):=Fin.cons (delta a) (fun j=> unfoldX (X j))
     let z:=unfoldX y; have hv:f i.succ=mountain z:=by simp only [f, Fin.cons_succ,X, update_self]; funext j; simp [cliff,mountain,z,unfoldX]
     change wholeX p f=0; have hh : update f i.succ (mountain z)=f:=hv ▸ update_eq_self ..; rw [← hh]; apply crest_zero _ hp h f _ z (fun _=>0) (by simp) (fun j _=>?_) (quietZ y)
     exact Fin.cases (by simp [f,quietX a]) (fun i=>by simpa only [f,Fin.cons_succ] using! quietZ (X i)) j
end YM.OPE.Silt.Phere

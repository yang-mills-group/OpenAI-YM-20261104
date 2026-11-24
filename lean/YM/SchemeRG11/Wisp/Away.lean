import YM.SchemeRG11.Wisp.Osc
/-! Close global charge. Neighbourhood fine.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.North
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels Outlook
open scoped Classical Matrix.Norms.Frobenius
variable {G:Gauge} {χ:Cover→ℝ}{s:Finset Cover}{m n:ℕ}
lemma civic (u:G.El)(p:pLabel G)(h:Neutral p) : vary (tide u) (nebula χ s p)=nebula χ s p:=by
 have he (x:Cover)(i j:Axis): vary (tide u) (Tree.cost x i j)=Tree.cost x i j:=by
    apply viewers; intro A; rw [tints_eval,supper,supper]; congr 1; unfold First.costVertex; split
    · rw [← signFace, ← signFace,← signLeap,← signLeap, mileC,Bark.leap,Bark.leap,cohort_p]; simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,←map_add,G.norm_adjoint]
    rfl
 have hh: vary (tide u) (escort χ s)=escort χ s:=by simp only [escort,map_sum,map_smul,he]
 rw [nebula,map_add,map_sub,←broiled,←broiled,map_mul,map_mul,hh,colored_v _ _ h,blast _ _ h,foliate _ _ h]
lemma terra (p:pLabel G)(h:Neutral p) : Still (inlay _ n (nebula χ s p)):=by intro x u; rw [rise_cast,lump_tu, ← tints_eval,civic _ _ h,rise_cast]
def spume (p:pLabel G)(h:Neutral p)(s:Finset Cover)(χ:Cover→ℝ)(m n:ℕ): Eidolon (G:=G) n m:=⟨cliff inkAge m (horizontal n (inlay G n (nebula χ s p))), au (steady _ (terra p h)) (horizontally _)⟩
-- exact orth operation for vertical differences
lemma haleI(x:Sky G n→ℝ): ∃ f:Bevy G.Color,f∈team G.Color n∧ linkup f=lump x:=by
 let L:= ∑ i,x i • plume i; refine ⟨L,Submodule.sum_mem _ (fun i _=>Submodule.smul_mem _ _ (team_height i.1.fst.isLt (clouded i))),?_⟩
 unfold L; rw [map_sum]; simp only [map_smul];rfl
lemma formatI(v:Sky G n)(hv:¬lineP v): ∃ p:Plane G.Color,p∈cap G.Color (inkAge v+1) ∧ p 0=0 ∧ ascent p = plum v:=by
 obtain ⟨p,hp,h,e⟩:= plunges _ hv; refine ⟨fun x=>p x-p 0,Submodule.sub_mem _ hp ?_,by simp,?_⟩
 · apply cap_height (show (1:ℕ) ≤ inkAge v+1 by omega) 
   intro s hs; obtain ⟨r,rfl⟩:=gather s hs; rw [show r=Fin.cons (r 0) (Fin.tail r) from Eq.symm (Fin.cons_self_tail ..),tract,fleet_cons', Multiset.card_eq_zero.mp (cargo _),fleet_zero,one_mul]; funext x; rw [soar_apply]; simp
 funext x; change (p _-p 0)-(p _-p 0)=_; rw [sub_sub_sub_cancel_right]; unfold plum; rw [←e]; rfl
variable (n)
lemma singleI(v:Sky G n):lump (Pi.single v 1)=plum v:=by rw [lump,Finset.sum_eq_single_of_mem v (Finset.mem_univ _) (fun _ _ e=>by rw [Pi.single_eq_of_ne e,zero_smul]), Pi.single_eq_same,one_smul] -- check
lemma ventI(q:vellum G)(v:Sky G n): vent (basisU v) (inlay G n q)=inlay G n (vent (cant (plum v)) q):=by rw [varyVent]; simp_rw [vane_tr, basisU, singleI]
lemma verticalI (p:pLabel G) :∃ t:Finset (Shaft G),∀ (χ:Cover→ℝ)(s:Finset Cover),covers χ s→t⊆parade s→(∀ i∈t,χ i.1.1=1)→∀ (v:Sky G n)(f:Plane G.Color), f 0=0 → ascent f=plum v → vent (basisU v) (inlay G n (nebula χ s p))= inlay G n (gas χ s p f):=by
 obtain ⟨t,hp⟩:= zeroPoint p; refine ⟨t,fun χ s h a b v f e g=>?_⟩
 rw [ventI,←g]; apply MvPolynomial.funext; intro x; obtain ⟨F,hF,H⟩:=haleI x; simp_rw [←aeval_eq_eval,rise_cast,←H]; exact hp _ _ h a b f e n F hF
end YM.SchemeRG11.North

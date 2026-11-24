import YM.RegulatorIR.Binding.Brand

/-! Close packet bookkeeping and expose the Ward-pruning invariant. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {G:Gauge}{E I J L X Y Z:Type}[Fintype E][Fintype I][Fintype J][Fintype L][Fintype X][Fintype Y][Fintype Z]
variable {m:ℕ} {T:Viewport G I}{Q:Viewport G J}{W: Transfer I L G}{F M:Hook G E I}
  {R: Hook G L J} {s:ℕ} {P:Medium G I Y}{N:Medium G J Z}{a:Y↪X}{b:Z↪X}{A B:Layer X X}{U:Orders X}
-- expand mark horizon bound for green and revert exactly
lemma paintMark (K:Law (Meadow G L))(d:X→Module.Dual ℝ (Meadow G L))(V U: Orders X)(w:X→ℝ)(h:Vacuum V)(hh:gradedSymmetric V)(ht:∀ e, Within (e+m) (U e))(hp:gradedSymmetric U):
 let T:= expo (rated (fun i=>i+2) V); let μ:=tangent G L; let A:=Diagram.Gaussian.bond K d; let R:= fun i=>i+m; Diagram.burn K d μ (T*rated R U) w= Diagram.burn K d μ T w * flavor m w (endHeat m A (logHeat A V true) U):= by
 intro T μ A R; let E:=endHeat m A (logHeat A V true) U
 have hv':∀ e,Within (e+(m+1)) (U e):= fun e r h=> le_trans (ht e r h) (by omega)
 have hp':endHeat (m+1) A (logHeat A V true) U=E:=by
    ext1 e;ext1 r; unfold E endHeat heated; dsimp only; symm; refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
    intro i _ he; rw [Finset.mem_range] at he; by_contra! h'; have := (Diagram.marked_cap m A V h U ht true e r i h').2; omega
 have he' (F:Orders X)(ht:∀ i,Within (i+m) (F i)): rated R F=rated (fun i=>i+m+1) F:=by ext1 i;rw [rated_v,rated_v];exact pack_extends (ht i) (Nat.le_succ _)
 have H':= Diagram.green K d (tangent G L) m V U w h hh hv' hp; dsimp only at H'
 change _= _*map _ (rated _ (endHeat (m+1) A _ _)) at H'
 rw [hp'] at H'; unfold flavor; change _= _* PowerSeries.map _ (rated R E); rw [he' E (Cluster.end_ranks m true ht h),he' U ht]; exact H'
omit [Fintype X][Fintype Z] in
lemma draftedVac (b:Z↪X)(B:Layer X X)(W: Orders X)(h:Vacuum W): Vacuum (collectO b B W):=fun e i he=> h e i (fun hf=> he (by unfold collectO; rw [hf,draft_void]; rfl))
where
 draft_void : ∀ i, draft B (0:Packet X i)=0:= fun i=> by
   have hv(l: List (Fin i)) : drawing (0:Packet X i) B l=0:=by induction l with
    | nil=>rfl
    | cons a l ih=>rw [drawing,ih,ray_zero]
   rw [draft,hv,sym_zero]
omit [Fintype X][Fintype Z] in
lemma inked (b:Z↪X)(B:Layer X X) (W:Orders X)(h:∀ i, Within (i+m) (W i)) e: Within (e+m) (collectO b B W e):=fun r he=> h e r (fun hz=> he (by unfold collectO; rw [hz,draftedVac.draft_void]; rfl))
omit [Fintype X][Fintype Z] in
lemma colorful (b:Z↪X)(B:Layer X X) (W:Orders X): gradedSymmetric (collectO b B W):=fun i j=>crop_symm b (draft B (W i j)) (is_symmetry _)
omit [Fintype X] in
lemma eraseVac (W:Orders X)(h:Vacuum W):Vacuum (pulp W):=fun i j he=> by unfold pulp at he; split at he; contradiction; exact h _ _ he
omit [Fintype X] in
lemma erased (W:Orders X) (h:gradedSymmetric W): gradedSymmetric (pulp W):=by intro i j; unfold pulp; split; exact symmetric_zero; exact h i j
omit [Fintype X] in
lemma warmed (A: Layer X X)(V:Orders X)(h:Vacuum V) : Vacuum (ceaseHeat A V true):=by intro e i he; unfold ceaseHeat heated at he; obtain ⟨k,_,hk⟩:=Finset.exists_ne_zero_of_sum_ne_zero he;exact ⟨(Diagram.heated_cap A V h true e i k hk).1,(Diagram.heated_cap A V h true e i k hk).2.1⟩
namespace Clip
variable (C:Clip (V:=W) (F:=R) P N a b A B U)
variable (h:Stead T F)(hp:Move T Q W R)
variable {D E':Orders Y}{ξ:ℝ⟦X⟧}

def prescribe (_C:Clip (V:=W) (F:=R) P N a b A B U) (D:Orders Y): Orders Z:= Diagram.collectO b B (ceaseHeat A (supply D a U) true)
def recurrent (C: Clip (V:=W) (F:=R) P N a b A B U)(D:Orders Y) (ξ : ℝ⟦X⟧):ℝ⟦X⟧:= ξ* PowerSeries.C (morning G L * sizes C.law)* expo (Binding.out (C.prescribe D))
def stencil (_C:Clip (V:=W) (F:=R) P N a b A B U)(m:ℕ)(D E : Orders Y): Orders Z:= collectO b B (endHeat m A (logHeat A (supply D a U) true) (Cluster.present a E))

variable (H:Dusk s F M P D ξ E' m)
include h hp H
lemma smokeRed (w:Meadow G J): manuscript (fuse W F R) 1 w=PowerSeries.C (Real.exp (-N.kinetic w))* recurrent C D ξ*expo (flavor 2 (N.color w) (pulp (prescribe C D))):=by
 let T:=supply D a U;let g:=announce B (dilute b (N.color w));let D':= prescribe C D
 let V:=ceaseHeat A T true; have hv: Vacuum T:= order_supply H.vacuum C.order
 have hs: Vacuum D':= draftedVac _ _ _ (warmed A T hv)
 rw [show manuscript (fuse W F R) 1 w= _ from cashThrough C h hp shapeOne (C.direction ξ w) _ w (C.combination H w), Diagram.red C.law C.directions (tangent G L) T g hv (sort_supply H.faces C.symmetry),Formal.map_exp, C.covariance]
 have hm : coeff 0 (Binding.out D')=0:=by unfold Binding.out; rw [PowerSeries.coeff_mk, vacuum_lo D' hs];rfl
 change _* expo (flavor 2 g V)= _
 rw [flavor_collect b V B (N.color w)]; change _*expo (flavor 2 _ D')=_
 rw [flavor_pulp D',timble_exp (flavor_dark _ (vacuum_lo _ (eraseVac D' hs)) _) hm,recurrent, direction,map_mul]; unfold D'; ring
lemma dust (H':Tune M) (w: Meadow G J): manuscript (fuse W F R) (blade J W M) w=
     manuscript (fuse W F R) 1 w * PowerSeries.X^s * flavor m (N.color w) (C.stencil m D E'):=by
 let V:=supply D a U;let T':= Cluster.present a E';let f:= N.color w; let g:=announce B (dilute b f);let Γ:= C.law
 let μ:= tangent G L; let ξ':= expo (rated (fun i=>i+2) V); let b':= flavor m g (endHeat m A (logHeat A V true) T'); let p:=C.direction ξ w
 rw [cashThrough C h hp H' (p*PowerSeries.X^s) _ w (C.combination_mark H w),show manuscript (fuse W F R) 1 w= _ from cashThrough C h hp shapeOne (C.direction ξ w) _ w (C.combination H w)]
 have hv:= paintMark Γ C.directions V T' g (order_supply H.vacuum C.order) (sort_supply H.faces C.symmetry) (Cluster.ranks_offer a E' H.since) (Cluster.sym_offer a E' H.goals);dsimp only at hv
 unfold Γ at hv; rw [C.covariance] at hv
 change _*Diagram.burn Γ C.directions μ _ g=_
 rw [show Diagram.burn Γ C.directions μ (ξ'*_) g= Diagram.burn Γ C.directions μ ξ' g * b' from hv]
 rw [show flavor _ _ (C.stencil _ _ _) = b' from (flavor_collect ..).symm];change p * _ * _*_=p* PowerSeries.C _*Diagram.burn Γ C.directions μ ξ' g * _ * _; ring
lemma victory (H':Tune M) : Dusk s (fuse W F R) (blade J W M) N (pulp (prescribe C D)) (recurrent C D ξ) (C.stencil m D E') m:= by
 let V:=supply D a U; have hv:Vacuum V:= order_supply H.vacuum C.order
 refine ⟨C.smokeRed h hp H,C.dust h hp H H', ?_,eraseVac _ (draftedVac b B _ (warmed A V hv)), erased _ (colorful _ _ _),inked b B _ (Cluster.end_ranks m true (Cluster.ranks_offer a E' H.since) hv),colorful _ _ _⟩
 have hh (f g:PowerSeries ℝ): coeff 0 (f*g)=coeff 0 f*coeff 0 g:=by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul]
 rw [recurrent, hh,hh,exp_start, mul_one]
 rw [PowerSeries.coeff_zero_C];exact mul_pos H.awake (mul_pos (dawn ..) (sizes_pos C.law))
end Clip
end YM.RegulatorIR.Binding

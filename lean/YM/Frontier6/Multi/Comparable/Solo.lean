import YM.Frontier6.Multi.Comparable.Combine

/-! The passing-leaf budget also handles an exact P field re-presented at
   *physical* grades with charges on each actual grade. Limits in a single
   ultrafilter under all choices of moving horizon/copies. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word Fareway
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{I V:Type}{C:Family G}{H:Extraction.Order}{S: Table C.book}{T:Fareway I}
variable (K: Final C H S){ξ:Ultrafilter (ℕ×ℕ)}{j k:I→ℕ} (hξ:ξ.toFilter≤ H.fuse) (hc:Extraction.Wcmain C){a b ε:ℝ}
variable (d:ℕ)(A:S.Field d)
set_option quotPrecheck false

lemma Fareway.Costs.mapped {T:Fareway I}{X Y 𝕜:Type*}[NontriviallyNormedField 𝕜][SeminormedAddCommGroup X][SeminormedAddCommGroup Y][NormedSpace 𝕜 X][NormedSpace 𝕜 Y]{u:I→X}{a:ℝ}(h:T.Costs u a) (L:X→L[𝕜] Y): T.Costs (fun i=> L (u i)) a:=by
    have hh:T.Costs (fun i=> L (u i)) (0+a):= (Fareway.Costs.const (T:=T) ‖L‖).coordinated h _ (Eventually.of_forall fun i=>by rw [Real.norm_of_nonneg (norm_nonneg L)]; exact L.le_opNorm _)
    rw [zero_add] at hh; exact hh


include hξ hc
lemma ticket_L (B:C.label d)(hk:Bench C.S T k b)(hε:0 < ε) : Permit K T ξ j k (fun _ x=> Tale.letter S x ⟨d,S.project d B⟩) (((d:ℝ)+ε)*b):=by
    let Y:Plan C Unit (fun _=>Unit):=⟨fun _ _=>0,fun _ _=>⟨d,B⟩,fun _=>1⟩
    obtain ⟨A,hA,hV⟩:= hc d (1+‖B‖) ε (by positivity) hε
    let w i := A*C.S.a (k i)^(-(d:ℝ)-ε)
    have he:T.Mint (fun i=>C.S.a (k i)^(-(d:ℝ)-ε)) (((d:ℝ)+ε)*b):= (hk.spacing.powers (-(d:ℝ)-ε)).eq (by ring)
    have hu(k':ℕ)(v): Y.syntaxR k' v S=Tale.letter S v ⟨d,S.project _ B⟩:=by unfold Plan.syntaxR Plan.point Plan.letter Plan.fee Y assembly; simp [Schedule.gridPoint]; change Tale.letter S (0+v) _=_; rw [zero_add]; rfl
    refine ⟨Unit,inferInstance,(fun _=>Unit),fun _=>inferInstance,(fun _:I=>Y),w,fun u v=>?_,(by simpa only [zero_add] using! (Costs.const A|>.mul he.pay)),?_⟩
    · convert! (Costs.free (X:=E4) (T:=T) (a:=-1)) using 2; ext; simp [Schedule.gridPoint,Y]; -- goal
    filter_upwards [hk.infinite.eventually_ge_atTop (C.ref d),he.pos] with i hi h;
    refine ⟨(fun _ _ _ _ _=>rfl), mul_nonneg hA h.le,?_,fun v=> by rw [hu]; exact Tale.almost K _⟩
    unfold Centered; refine (Eventually.filter_mono hξ ((Push.RelayDifference.cutoff_grows H).eventually (hV (k i) hi))).mono (fun p h=>?_)
    obtain ⟨hN,_,hL⟩:= h p.2 B (by linarith only); change ∃ h, _; refine ⟨hN,?_⟩; dsimp only; rw [show Y.cost (j i) p.1 p.2=C.O p.1 p.2 B 0 from ?_]; exact hL 0;
    funext U; unfold Plan.cost; simp only [Y,Fintype.sum_unique, Fintype.prod_unique,one_mul]; rw [location_origin];
lemma ticket_F (hk:Bench C.S T k b)(hε:0<ε): Permit K T ξ j k (fun _ x=> Tale.letter S x ⟨d,A⟩) (((d:ℝ)+ε)*b):=by obtain ⟨q,rfl⟩:= S.onto d A; exact ticket_L K hξ hc d q hk hε
local notation "J"=>Fin (Module.finrank ℂ (S.Field d))
lemma ticket_focus (hk:Bench C.S T k b)(hε:0<ε)(V:I→S.Field d) (hv:T.Costs V a): Permit K T ξ j k (fun i x=> Tale.letter S x ⟨d,V i⟩) (((d:ℝ)+ε)*b+a):=by
   let g:=Module.finBasis ℂ (S.Field d); let v (i:J) := LinearMap.toContinuousLinearMap (g.coord i); let F(i):(BasisRay S I):=fun s x=> v i (V s) • Tale.letter S x ⟨d,g i⟩
   refine (Permit.sums hξ F Finset.univ (fun i _=> (ticket_F K hξ hc d (g i) hk hε).scale (hv.mapped (v i)))).same (Eventually.of_forall (fun i x=>?_))
   change Congr K (∑ j:J,v j (V i) • _) _; have hp:= combine_letter K x d (fun j:J=>g j) (fun j:J=>v j (V i)); rw [show ∑ j:J,v j (V i) • g j=V i from g.sum_repr _] at hp; exact hp
end YM.Frontier6.Road

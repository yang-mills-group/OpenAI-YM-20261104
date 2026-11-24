import YM.MSbar.Diagram.Layer
/-! Lap discharge at positive-dimensional momenta and analytically (Market) in the native space.
Includes bilinear evanescent slots of all marks in Ward identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {I:Finset C} {W:Edition C} {m k j n:ℕ} {U:Set ℂ}
  {f g:Functionals C} {L P A:Links C} {d e l : Bit}

lemma proper (v: Grow C m): lapSum W L f m m v= dotted (W.members m) (L m m) (f m m) v.2 v.1 := by
    let L0:= lapSum W L f m; unfold lapSum dotted; simp_rw [tread, Domain.discrete,Edition.sum]; simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a h
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x hx; refine Finset.sum_congr rfl fun b hb=> Finset.sum_congr rfl fun y hy=> ?_
    unfold edge; dsimp; ring

-- true measure in all pairs dimensions. Use no density normalization except DR prescription
abbrev actual (m:ℕ): Measure (Mom m) := ENNReal.ofReal (DR.mass m) • volume
lemma actual_nn (m:ℕ) : ENNReal.ofReal (DR.mass m) ≠⊤:= ENNReal.ofReal_ne_top
instance (m:ℕ) : IsLocallyFiniteMeasure (actual m):= by exact isLocallyFiniteMeasureSMulNNReal volume (Real.toNNReal (mass m))
lemma available (m:ℕ) : Nonempty (Snap (Mom m) (actual m)):= by obtain ⟨A⟩:= Edition.lattice m; exact A.mass _ (mass_pos m).le
lemma lap_at (W:Edition C){z:ℂ} {L':Links C}{F' : Functionals C}(hL:L z=L' z)(hF:f z=F' z): Lap W L f z= Lap W L' F' z:=by
   have h (a b:C): tread W a b L f z=tread W a b L' F' z:=by
      unfold tread; congr! 1; unfold edge; rw [hL,hF]
   have H: lapSum W L f z=lapSum W L' F' z:=by unfold lapSum; simp_rw [h]
   exact congr_arg (fun (S:∀ m,Grow C m→ℂ)=>turn (line C) z S) H
variable (h : Full U k W d f) (hp : Pilot U j W e L) {R:ℝ} (hB:Band U L R) (hR:0 ≤ R) (hz:(m:ℂ)∈U)
include h hp hB hR hz
lemma nominal : Lap W L f m m = Loops.loop (actual m) (W.members m) (L m m) (f m m) := funext fun v=>
   ((situated h hp hB hR).integer hz v).trans (integral_congr_ae (Eventually.of_forall fun t=> proper (f:=f) (W:=W) (L:=L) (v,t)))
lemma available_tag : Homogeneous (lift (W.binary m)) (e+d) (Lap W L f m m):= by
   obtain ⟨s⟩:= available m; rw [nominal h hp hB hR hz]; exact Supported.bears s (Domain.supported hp hB hz) (hp.pace hz) (fares h.licensed hz) (h.quiet _ hz _) (h.span _ hz m)
lemma integrable (v:Words C m): Integrable (fun p:Mom m=>dotted (W.members m) (L m m) (f m m) p v) (actual m):=by
   obtain ⟨h,hZ⟩:= (situated h hp hB hR).pays m hz m v
   rw [show (fun p:Mom m=> dotted _ _ _ p v)= (fun p=> lapSum W L f m m (v,p)) from ?_]; rotate_left; exact funext fun p=>Eq.symm (proper (v,p)); exact h.1.continuous.integrable_of_hasCompactSupport (hZ.compact)
lemma traced_color : Polar W (Lap W L f m m):=by
    rw [nominal h hp hB hR hz]; intro c p a b; let r(y:Hat m):Words C m:= a++((c,y),p)::b; let W'(u:Mom m)(y:Hat m):= dotted (W.members m) (L m m) (f m m) u (r y)
    have ht(u:Mom m): Dim.One (W.vector c) (W' u) := by
       refine one_sum (W.members m) fun i hi=> one_sum (W.members m) fun j hj=> ?_
       exact (h.colors m hz m c p ((i,u)::(j,-u)::a) b).scale _
    have hf(y): Integrable (fun x=> W' x y) (actual m):= integrable h hp hB hR hz _
    let g(v):= ∫ x,W' x v ∂actual m; change Dim.One _ g; unfold Dim.One; split_ifs with H
    · choose A he using fun u=> (show ∃ F : Hat m →ₗ[ℝ]ℂ, ∀ x,W' u x=F x by have h:= ht u; simpa [Dim.One,H] using h)
      refine ⟨{toFun:=g,map_add':=fun a b=>?_,map_smul':=fun c x=> ?_},fun _=> rfl⟩
      · have hp (u) : W' u (a+b)=W' u a+ W' u b:= by simp_rw [he]; rw [map_add];
        unfold g; simp_rw [hp]; exact integral_add (hf _) (hf _)
      have hp(u): W' u (c • x)=c • W' u x:= by simp_rw [he]; rw [map_smul]
      unfold g;simp_rw [hp]; exact integral_smul ..
    refine ⟨g 0,fun x=> integral_congr_ae ?_⟩; filter_upwards with v; have hh := ht v; unfold Dim.One at hh; rw [if_neg H] at hh; exact (hh.choose_spec x).trans (hh.choose_spec 0).symm
omit hz in
lemma payload (hu:IsOpen U): Full U (1+(j+k)) W (e+d) (Lap W L f) := by
   have hS:= budget h hp hB hR hu; refine ⟨hS.safe,hS.quiet,?_,?_⟩
   · intro t hz m; let F(t':ℂ) := f t; let L'(t':ℂ):= L t; have ho:=h.freeze hz; have hz':= hp.freeze hz; have he:Band univ L' R:= fun _ _=> hB _ hz
     have ht : Polar W (Lap W L' (fun _=>f t) t m):= (budget ho hz' he hR isOpen_univ).choose_color W (fun n=> traced_color ho hz' he hR (mem_univ _)) t
     rw [lap_at W (show L t=L' t from rfl) (show f t= F t from rfl)]; exact ht
   intro t hz m; let F(t':ℂ) := f t; let L'(t':ℂ):= L t; have ho:=h.freeze hz; have hz':= hp.freeze hz; have he:Band univ L' R:= fun _ _=> hB _ hz
   have ht : Homogeneous (lift (W.binary m)) (e+d) (Lap W L' (fun _=> f t) t m):= (budget ho hz' he hR isOpen_univ).choose_hom W (fun n=> available_tag ho hz' he hR (mem_univ _)) t
   rw [lap_at W (show L t=L' t from rfl) (show f t= F t from rfl)]; exact ht
end YM.MSbar.Diagram

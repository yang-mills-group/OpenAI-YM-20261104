import YM.FVA2.StripWalk
/-!
# Each slot contributes the engineering-graded single-jet answer in MS notation
-/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.FVA2.Plate
open Filter Topology Set Function MeasureTheory Maxwell Tensor
open Wilson Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book
open MS.Cylinder MS.Plane MS.Tone MS.Tone.Frame MS.Color
open RG PertExtension MvPolynomial
open Next.Rank Next.Rank.CellsInt Next.Rank.Spindle MS.Theater
open Next.Rank.Configuration Next.Foundations Labels
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{d n:ℕ}
local notation "W"=>Lattice.Cover
local notation "print"=> YM.PertExtension.Heat.Ray.print
local notation "address"=>YM.PertExtension.Heat.Ray.address
lemma print_X (a:Beast G) (d):
 print d (X a)=∑ j:KeyIn G d, ((Beamer.tester j.val (address a):ℝ):ℂ) • X j.val:= by
 unfold YM.PertExtension.Heat.Ray.print; rw [AlgHom.comp_apply,Normal.exchange_x]; simp only [Normal.glyph,LiftMark.ink,map_sum,Finsupp.linearCombination_single,map_smul,rename_X]
-- linear basis footprint
lemma tier_X (i: Labels.Key G) (s:ℕ): tier s (X (R:=ℂ) i)=if Labels.generation i=s then X i else 0:= by
   unfold tier; split; · next h=> rw [← h]; exact (MvPolynomial.isWeightedHomogeneous_X _ _ _ |>.weightedHomogeneousComponent_same)
   next h=> apply (MvPolynomial.isWeightedHomogeneous_X _ _ _ |>.weightedHomogeneousComponent_ne); exact Ne.symm h

lemma far_jets (n d:ℕ)(a:Beast G) (hn:n+2≤d):
   tier (n+2) (print d (X a))= page n (G:=G) (Complex.ofRealCLM.toLinearMap ∘ₗ (LinearMap.proj (address a) ∘ₗ Beamer.sweep n)):= by
    -- all components by Sigmas
    unfold page; rw [print_X,map_sum]; simp_rw [ map_smul,tier_X,smul_ite,smul_zero ]; rw [ ← Finset.sum_filter ];
    let φ (j: Fin (Labels.dim G n)): KeyIn G d:= ⟨ ⟨ n,j ⟩,hn ⟩; symm; apply Finset.sum_bij (fun i _=>φ i)
    · intro i hi; simp [φ,Labels.generation]
    · intro i hi j hj h; exact eq_of_heq (Sigma.mk.inj ( congr_arg Subtype.val h )).2
    · rintro ⟨ ⟨i,j⟩,hi⟩ H; simp only [Finset.mem_filter] at H; have he:i+2=n+2:=H.2; obtain rfl:i=n:=(by omega); exact ⟨j,Finset.mem_univ j,rfl⟩
    intro i _; rfl
lemma single_price (a:Beast G)(n:ℕ)(T:Labels.Taylor G n): corner (rope (step_in G n T)) a.1.plaq a.1.offset a.2 = Beamer.sweep n T (address a):= by
   let i:= a.1.plaq.val.1; let j:= a.1.plaq.val.2; let x:= a.1.offset; apply congr_arg (fun v:G.Color=> v a.2) (show corner (rope (step_in _ _ T)) a.1.plaq x=test T i j x from ?_); rw [cigar]; unfold corner; change trail T i x + trail T j (x+Lattice.step i)-trail T i (x+Lattice.step j)-trail T j x=_; unfold stepValue; dsimp only [Pi.sub_apply]; abel
lemma ray_atom (a:Beast G) (i:Axis)(p:QP)(c:G.ColorIndex)(n d:ℕ) (h:n+1≤d):
    (Theater.orbit G (tier (n+1) (print d (X a)))) [waveForm p i c]= reading n (fun t:ℝ => delay (t • p) i * beacon a (waveForm (t • p) i c)) := by
    cases n with
    | zero=>
       rw [print_X,map_sum]; simp_rw [map_smul,tier_X,show ∀ j:Labels.Key G,Labels.generation j≠ 0+1 from fun j=>by unfold Labels.generation; omega, ite_false,smul_zero]; rw [Finset.sum_const_zero,map_zero,credit_curve,rope_zero_grade]; simp
    | succ n=>
       let F :Feet G (n+1):= speak (n+1) i p (cl G c); rw [far_jets n d a (by omega),pageX,credit_curve]; change hitϑ (n+1)* ( ↑((Beamer.sweep n (yard G n F)) (address a)):ℂ) = hitϑ (n+1)*( ↑(corner (rope F) a.1.plaq a.1.offset a.2):ℂ ); rw [← single_price,taxiY, clear_grad]
lemma off_lanes (t:Beast G)(k n:ℕ)(x:List (Lane4 G)) (ht:¬∃ (i:Axis)(p:QP)(c:G.ColorIndex),x=[waveForm p i c]):
    Theater.orbit G (tier k (print n (X t))) x=0:= by
   rw [print_X,map_sum,map_sum, Finset.sum_apply]; apply Finset.sum_eq_zero; intro j _; rw [ map_smul,tier_X ]; split_ifs with hj; swap; · rw [smul_zero,map_zero]; rfl; -- fix
   rw [map_smul,cusp]; rcases x with _|⟨⟨⟨⟨_|i,_|_⟩,s⟩,p⟩,_|_⟩ <;> first| exact (ht ⟨_,_,_,rfl⟩).elim | exact mul_zero _
end YM.FVA2.Plate

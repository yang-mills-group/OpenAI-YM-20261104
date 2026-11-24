import YM.X.Rank.Cash
/-!
# All contractions on primary polynomials are silent

Nested finite list of paired flavor/color Laplacians. We never use a linear response
of higher horizon than that of the field space being normalized. To see a silent pair
after hitting the old test operating on primary **and** an arbitrary number of local probes,
flatten slit directions at the probe insertions. Thus contact between auxiliary bilocal
probes need not be retained or estimated.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial Rad
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {s : Finset Stroke} (c : G.ColorIndex) {P : Canvas G}

lemma Silent.wears (h:Silent c P S)(W : List Scout)(hp:adm S W) : Silent c (clothe W * P) (S∪loci W) := by
   intro v hv; obtain ⟨v₁,v₂⟩:=hv; rw [← mul_assoc,show clothe (G:=G) v*clothe W=clothe (v++W) by simp [clothe]]; apply h (v++W)
   simp only [adm,List.map_append,loci,List.toFinset_append, List.nodup_append] -- edit
   obtain ⟨w1,w2⟩:=hp; simp [v₁,w1]; refine ⟨?_,v₂.mono_right Finset.subset_union_left,w2⟩; rintro a x x₁ _ y y₁ rfl; apply Finset.disjoint_left.mp v₂ (show a∈loci v from List.mem_toFinset.mpr (List.mem_map_of_mem (f:=Prod.fst) x₁)) (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem (f:=Prod.fst) y₁)))
lemma Fits.Lap (hp:Fits (S:Set E4) P)(x y:Stroke→ℂ): Fits (S:Set E4) (Rank.Lap x y P):= by rw [lap_at]; exact Subalgebra.sum_mem _ fun _ _=> slit_stays _ (slit_stays _ hp)
lemma Silent.Lap (h:Silent c P S)(hp:Fits (S:Set E4) P)(x y:Stroke→ℂ): Silent c (Rank.Lap x y P) S:= by
  intro W hw; let I:=S∪loci W
  have hh: Silent c (clothe W * P) I:= Silent.wears c h W hw
  let f (x:Stroke→ℂ)(a:Stroke):= if a.1∈S then x a else 0
  have he (a:Stroke→ℂ)(Q:Canvas G)(h':Fits (S:Set E4) Q)(i:G.ColorIndex): slit (dip (f a) i) Q=slit (dip a i) Q:=by refine slit_congr _ _ _ h' ?_ ; rintro z hz; simp [f,dip,show z.1.1∈S from hz]
  have hx (a : Stroke→ℂ)(i:G.ColorIndex)(Q:Canvas G)(h':Fits (S:Set E4) Q): slit (dip (f a) i) (clothe W*Q)=clothe W*slit (dip a i) Q:=by
    rw [Derivation.leibniz,he _ _ h' i,slit_dark (f a) i (fun j hj=> ?_),smul_zero,add_zero,smul_eq_mul]
    exact if_neg (fun hq=> Finset.disjoint_left.mp hw.2 (mem_supported.mp (wear_fits (G:=G) W (fun _ hh=> hh)) hj) hq)
  have hf : Fits (I:Set E4) (clothe W*P):= Subalgebra.mul_mem _ (wear_fits W fun i hi=> Finset.mem_union_right _ hi) (Fits.incl hp Finset.subset_union_left)
  rw [lap_at, Finset.mul_sum]; convert Rank.Lap_zero c (f x) (f y) hh hf using 2; rw [lap_at]; simp_rw [hx y _ _ hp, fun i:G.ColorIndex=>hx x i _ (slit_stays _ hp)]
end YM.PositionX.Rank

import YangMills.WilsonProof.NativeSupport.YM.MS.Wilson.DyedAction
/-!
# Invariant Lap and bracket at stencil

Use finite periods with actual dtraces. No grading relation spaces. Need mark sense.
    This avoids reproving ambiguity of translation density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Paint
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Bare Focus Landau Sew Chart Draft
open Lattice Color
variable {G:Gauge} {P I:Type}
namespace Colorless
variable {F H : Dot G P}
lemma add (h:Colorless F)(h':Colorless H): Colorless (F+H):=fun u=> by rw [map_add,h u,h' u]
lemma sub (h:Colorless F)(h':Colorless H):Colorless (F-H):=fun u=>by rw [map_sub,h u,h' u]
lemma csum {f:I→Dot G P}(J:Finset I)(h:∀i∈J,Colorless (f i)): Colorless (∑ i∈J,f i):= fun u=> by rw [map_sum]; exact Finset.sum_congr rfl fun i hi=> h i hi u
lemma smul (c:ℂ)(h:Colorless F): Colorless (c • F):=fun u=>by rw [map_smul,h u]
lemma couple (hF:Colorless F)(hH:Colorless H): Colorless (couple DotFlip F H):= fun u=>by rw [pigment, hF u,hH u]
end Colorless
variable (u:G.El)(F H:Dot G P)

lemma solok (x:P)(i:Atom Axis)(j:CI G): enter ((i,j),x) (dye u F)=∑ k:CI G, wc u j k • dye u (enter ((i,k),x) F):= palette (stripe G P) u (i,x) j F
lemma forward (i j:CI G): ∑ a,wc u a i * wc u a j= if i=j then 1 else 0:= by
    have he a b := wc_conjugate u a b; simp_rw [he,transposed]
lemma spanlap (x:P)(i j:Atom Axis): ∑ a:CI G, enter ((i,a),x) (enter ((j,a),x) (dye u F)) = dye u (∑ a:CI G, enter ((i,a),x) (enter ((j,a),x) F)):= by
    simp_rw [solok, map_sum,map_smul,solok,Finset.smul_sum, smul_smul]; -- check
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul,forward]; simp [ite_smul]
-- turn stem sum into contracted. Γ direction mixed Hess.
section finite
variable [Fintype P]
lemma spotlap (i j:Atom Axis): ∑ a:CI G, heart (i,a) (j,a) (dye u F)=dye u (∑ a:CI G,heart (i,a) (j,a) F):= by
    conv_rhs => arg 2; simp only [heart_all]; rw [Finset.sum_comm]
    simp_rw [map_sum,heart_all]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> by rw [spanlap]; simp
lemma lampC : (Spectrum G).Lap (dye u F)= dye u ((Spectrum G).Lap F):= by
    simp_rw [Bonded.lap_at,Fintype.sum_sum_type,Fintype.sum_prod_type];
    simp only [show ∀ (i:Axis)(j:CI G),((Spectrum G).fee (Sum.inl (i,j)):ℂ)=1 from fun i j=>rfl,show ∀ j:CI G,((Spectrum G).fee (Sum.inr j):ℂ)=-1 from fun i=>rfl, one_smul, map_add,map_sum] -- detect
    congr 1
    · apply Finset.sum_congr rfl; intro i _; rw [← map_sum]; exact spotlap u F (anti i) (Landau.gauge i)
    · rw [← map_sum]; simp_rw [← Finset.smul_sum,map_smul]; congr 1; exact spotlap u F (i:=gaugeC) (j:=ghost)
omit [Fintype P] in
lemma shade_twist (x:Bool): dye u (twisted DotFlip x F)=twisted DotFlip x (dye u F):= by
    let c:= stripe G P; exact (slender c u).twists (mood c u (p:=DotFlip) (fun i j h=> congr_arg Landau.p (show i.1.1 = j.1.1 from congr_arg (Prod.fst (β:=P)) (show (i.1.1,i.2)=(j.1.1,j.2) from h)))) x F
-- recover ∆ via val identity and move
lemma colorLap [AddCommGroup P] : dye u ((Spectrum G).touch F H)=(Spectrum G).touch (dye u F) (dye u H) := by
   let B:= Spectrum G; let Z:On (Branch G Axis) P ℂ:= B.Lap
   have he (F H:Dot G P) : B.touch F H= (Z (couple DotFlip (sumHome F) H)-couple DotFlip (Z (sumHome F)) H)-couple DotFlip (twisted DotFlip true (sumHome F)) (Z H):= by apply Subtype.ext; simp only [B.t_here,B,Z,Spectrum,Bonded.lap_here,coupled,twistp,Submodule.coe_sub,link] -- adjust
   have ht : dye u (sumHome F)=sumHome (dye u F):= by rw [total_uses,total_uses,map_sum]; apply Finset.sum_congr rfl; intro i _; exact (painting u F (fun z=>i+z)).symm
   rw [show (Spectrum G).touch F H=_ from he F H, show (Spectrum G).touch (dye u F) (dye u H)= _ from he ..]
   dsimp only [Z,B]; simp_rw [map_sub,pigment, ← lampC, ht, shade_twist u (sumHome F)]; rw [ht,pigment, ht]
end finite

variable (A S:Dot G Cover)
lemma originLap : dye u ((Spectrum G).Lap A)=(Spectrum G).Lap (dye u A):= by
    refine (markEq ..).mp ?_; filter_upwards [soon_heart (Spectrum G) (dye u A),soon_heart (Spectrum G) A] with n hn ha
    unfold shown at *; simp_rw [painting,ha,hn,painting,lampC]
lemma rootLap : dye u ((Spectrum G).touch A S)=(Spectrum G).touch (dye u A) (dye u S):= by
    refine (markEq ..).mp ?_; filter_upwards [soon_root (Spectrum G) (dye u A) (dye u S),soon_root (Spectrum G) A S] with n hn ha
    unfold shown at *; simp_rw [painting,ha,hn,painting,colorLap]
end YM.MS.Native.Paint

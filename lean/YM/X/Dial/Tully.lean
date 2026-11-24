import YM.X.Dial.Serve
/-!
# Integral link Taylor field stencil with signed H before reading W.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Dial
open Lattice Wilson Next.Rank Normal LiftMark MvPolynomial Function Stems Filter MeasureTheory Metric Interval Hinge Grow
open CellsInt Configuration Beamer Labels Source Drops Maxwell PertExtension LatticePT
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge}{k d:ℕ}(s:Signed) (Y:Taylor G k)
lemma vturn (i:Axis)(x:E4): (Taylor.turn s.ortho⁻¹ Y).value i x= digit s i • Y.value (s.perm i) (Ortho.motion s.ortho x):= by
    simp only [Taylor.turn_value,inv_inv,Ortho.motion_at]; rw [Finset.sum_eq_single_of_mem (s.perm i) (Finset.mem_univ _)]; swap; · intro j _ h; rw [show s.ortho⁻¹.val i j=star (s.matrix j i) from rfl]; simp [s.matrix_at,Ne.symm h]
    rw [show s.ortho⁻¹.val i (s.perm i)=star (s.matrix (s.perm i) i) from rfl]; simp [digit,s.matrix_at]
lemma motion_st (x:Cover): Ortho.motion s.ortho (mapZ x)=mapZ (s.act x):= by
    rw [Ortho.motion_at,Signed.ortho_move]; ext i; obtain ⟨j,rfl⟩:= s.perm.surjective i; cases h:s.flip j<;>simp [mapZ,h]
lemma motion_ab (i:Axis): Ortho.motion s.ortho (basis i) = digit s i • basis (s.perm i):= by
    ext z; obtain ⟨j,rfl⟩:=s.perm.surjective z; rw [Ortho.motion_at,Signed.ortho_move]; cases h:s.flip j <;> rcases eq_or_ne j i with e|hy<;>first | (subst i;simp [digit,h])|(cases ht:s.flip i<;>simp [digit,h,hy,ht]) -- edit

lemma motion_p (x:Cover)(i:Axis)(r:ℝ): Ortho.motion s.ortho (mapZ x+r • basis i)=mapZ (s.act x)+ r • (digit s i • basis (s.perm i)):= by rw [map_add, motion_st,map_smul,motion_ab]
lemma trail_v (x:Cover)(i:Axis): trail (Taylor.turn s.ortho⁻¹ Y) i x = digit s i • trail Y (landing s (x,i)).2 (landing s (x,i)).1 := by
    cases h: s.flip i with
    | false => rw [rotate_false s _ h]; unfold trail; simp only [comp_apply]; unfold CellsInt.east; simp only [vturn,motion_p, digit,h,Bool.false_eq_true,↓reduceIte,one_smul]
    | true=>
       rw [rotate_true s _ h]; unfold trail; simp only [comp_apply]; unfold CellsInt.east; simp only [vturn,motion_p,digit,h,↓reduceIte,neg_one_smul]; rw [intervalIntegral.integral_neg]; apply congr_arg
       let f:=fun t:ℝ=> Y.value (s.perm i) (mapZ (s.act x -step (s.perm i)) + t • basis (s.perm i)); have he(t:ℝ): mapZ (s.act x)+ t • -(basis (s.perm i)) = mapZ (s.act x-step (s.perm i))+ (1-t) • basis (s.perm i):=by
          have hr:=mapZ_step (s.act x-step (s.perm i)) (s.perm i); rw [sub_add_cancel] at hr; rw [hr]; module
       simp_rw [he]; change (∫ t in (0:ℝ)..1,f (1-t))=∫ t in (0:ℝ)..1,f t; rw [intervalIntegral.integral_comp_sub_left]; simp

def across (A:Labels.Jet G)(d:ℕ):Brush G:= Drops.access (Drops.trunk d A)
lemma span_across (A:Labels.Jet G)(i:Pin): across A d i=∑ j∈Finset.range (d-1), trail (A j) i.2 i.1:= by unfold across; rw [Spindle.revealed_cell]; refine Finset.sum_congr rfl fun j hj=>?_ ; simp only [Drops.expand,Drops.trunk, dif_pos (Finset.mem_range.mp hj)] -- namespace
lemma across_v (A:Labels.Jet G): Lbrush s (across A d)=across (changedJet (fun i=> Taylor.turn s.ortho⁻¹) A) d:= by
    funext i; rw [Lbrush_point,span_across,span_across,Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; exact (trail_v s (A j) i.1 i.2).symm
lemma across_print (A:Labels.Jet G)(p:poly (Atom G)): snap (across A d) (loom p)= Labels.read A (Heat.Ray.print d p):= by
    rw [Heat.Ray.display_jet,looms]; apply congr_arg (fun f:Atom G→ℂ=> aeval f p); funext i; apply congr_arg Complex.ofReal
    let A':=Drops.trunk d A; let z:=i.1.offset; let a:=i.1.plaq.val.1; let b:=i.1.plaq.val.2
    apply congr_arg (fun t:G.Color=>t i.2); change curl _ z a b = Exterior.linkSum _ z (square a b)
    simp only [Exterior.linkSum,square,Step.used,posDir,negDir,Step.vec,↓reduceIte,Bool.false_eq_true,add_zero, sub_eq_add_neg]; unfold curl across; rw [show z+step a+step b+ - step a= z+step b by abel,add_neg_cancel_right]; abel

lemma printed_v (s:Signed)(n:ℕ)(p q:poly (Atom G))(h:loom p=relay s (loom q)): Heat.Ray.print n p= rotated s.ortho (Heat.Ray.print n q):= by
    apply Labels.eval_ext; intro A; rw [rotated, eval_changed,← across_print (d:=n),← across_print (d:=n),h]; rw [read_snap, across_v]
lemma hp_rot (x:Axis:=0): 0 < (1:ℝ):=by norm_num
end YM.PositionX.Dial

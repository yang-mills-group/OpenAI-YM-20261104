import YM.X.Try.Wolf
import YM.X.Grow.Hue
import YM.X.Dial.Tully
import YM.Pert.Lattice.Lifts
/-! # Function on constant curvature panels. Exact across Ray. *Use only after grade cut*. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal LiftMark CellsInt Configuration MvPolynomial Function Filter Set Asymptotics Gauge
open Source Drops PertExtension LatticePT Gauge ProjectorNext.Calibration Maxwell Bid Hue Grow Clove Dial Next.Foundations Labels Spindle Tensor
open Stems hiding X
open Heat.Top hiding test
open scoped Topology ContDiff BigOperators Pointwise Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d n k:ℕ} {V I:Type*}
-- indep eval tests on flat panels
local notation "Ξ"=> CoverC G
local notation "L"=> Taylor G 0
variable (P:Labels.Taylor G 0)
def panel (G:Gauge) := PlaqAxes→G.Color
abbrev PanelL (G:Gauge):= Hue.Mask PlaqAxes G
abbrev curτ (P:Taylor G 0)(x:PlaqAxes):G.Color:=takeCurl P x.val.1 x.val.2 Fin.elim0
lemma τφ (U:PanelL G) : ∃ P:Labels.Taylor G 0, curτ P = U:= by
    let f(i j:Axis) := if h:i<j then ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _:Fin 0=> E4) (U ⟨(i,j),h⟩) else (0:T E4 G.Color 0); let Q(i j:Axis):= f i j-f j i
    have he : ClosedJet Q:= by
        refine ⟨fun i j v s=> congr_arg (Q i j) (Subsingleton.elim ..), fun i j=> by unfold Q; abel, fun i j k x=>?_ ⟩; simp_rw [show ∀ i j:Axis, diagonal (Q i j) = fun _=>Q i j Fin.elim0 from fun i j=>funext fun _=> congr_arg (Q i j) (Subsingleton.elim ..)]; simp [Maxwell.grad, Analysis.D]
    refine ⟨contracted he, funext fun i=> ?_⟩; rw [curτ, curl_inverse he]; unfold Q f; rw [dif_pos i.property,dif_neg (not_lt_of_ge i.property.le),sub_zero]; rfl
abbrev peek (P:Labels.Taylor G 0): poly (CoverC G)→ₐ[ℂ] ℂ:= Hue.display (curτ P)
lemma peek_ext {p q: poly (CoverC G)}(h:∀ X:Taylor G 0, peek X p=peek X q):p=q:= touchable fun x=> by obtain ⟨k,hk⟩:= τφ x; rw [← hk]; exact h k
def chunk (P:Labels.Taylor G 0): Labels.Jet G:= Pi.single 0 P
lemma glow_one (hd:1<d)(x:RG.Slot): glow (Drops.trunk d (chunk P)) x=curτ P x.plaq:= by
    let A:=Drops.trunk d (chunk P); let r:Face ℤ:=(x.offset,x.plaq); let i:=x.plaq.val.1; let j:=x.plaq.val.2
    change oneGlow d A r=_; rw [glows,Finset.sum_eq_single_of_mem 0 (by rw [Finset.mem_range]; omega)];
    · have he(w:Cover):CellsInt.test P i j w= curτ P x.plaq := by
           rw [← show jumps 0 Fin.elim0 (CellsInt.test P i j) w=CellsInt.test P i j w from rfl, test_top, Nat.factorial_zero, Nat.cast_one,one_smul]; exact congr_arg _ (Subsingleton.elim (α:=Fin 0→ E4) ..)
      change CellsInt.test (expand d _ 0) i j r.1=_; rw [show expand d A 0=P from ?_,he]; unfold A Drops.trunk expand chunk; rw [dif_pos (by omega)]; exact Pi.single_eq_same ..
    intro k hk he; rw [show expand d A k=0 by unfold A Drops.trunk expand chunk; rw [dif_pos (Finset.mem_range.mp hk)]; exact Pi.single_eq_of_ne he _]; unfold CellsInt.test foil; rw [show takeCurl (0:Taylor G k)=(0:TwoJet G.Color k) from congr_arg Subtype.val (potential.map_zero), show diagonal ((0:TwoJet G.Color k) r.2.val.1 r.2.val.2)=(fun _=>0) from rfl,east_const, east_const]; rfl
lemma peer (hd:1<n)(q:poly (Atom G)): peek P (lump q) = Labels.read (chunk P) (Heat.Ray.print n q):= by
    rw [Heat.Ray.display_jet,peek, display, lump, aeval_rename]; unfold Spindle.text; simp_rw [glow_one P hd]; rfl
lemma cut_view {q:Pol G}(h:HC q d)(ht:n=2*d) : Labels.read (chunk P) q=Labels.read (chunk P) (capRead n q):= by
    let J:=chunk P; let R:=level (V:=Labels.Key G) Labels.generation n; -- level generic
    simp_rw [← Heat.Ray.weigh]; change Labels.read J q=Labels.read J (R q); rw [q.as_sum,map_sum,map_sum,map_sum]; refine Finset.sum_congr rfl (fun i hi=>?_ ); by_cases he:Finsupp.weight Labels.generation i ≤ n
    · change _= Labels.read J (Rise.trim (MvPolynomial.monomial i _) _ _); rw [LiftMark.trim_mono, if_pos he] -- provide
    have hu:∃ j : Labels.Key G, j∈i.support ∧ 0< j.1:= by
        by_contra! hy; apply he; rw [ht, ← show degree i=d from h (mem_support_iff.mp hi), Finsupp.weight_apply, Heat.Top.degree_eq,Finsupp.sum,Finsupp.sum,Finset.mul_sum]; apply Finset.sum_le_sum; intro x hx; unfold Labels.generation; have ht:x.1=0:= by have ht:=hy x hx; omega
        rw [ht]; change i x * _≤2*i x; omega
    obtain ⟨j,hj,hz⟩:=hu; change Labels.read J _= Labels.read J (Rise.trim _ _ _); rw [LiftMark.trim_mono,if_neg he,map_zero]; unfold Labels.read; rw [MvPolynomial.aeval_monomial];unfold Finsupp.prod; rw [Finset.prod_eq_zero hj,mul_zero]; change Labels.coord J j ^ i j=0; rw [show Labels.coord J j=0 from ?_, zero_pow (n:=i j) (Finsupp.mem_support_iff.mp hj)]; unfold Labels.coord J chunk; rw [Pi.single_eq_of_ne (Nat.ne_of_gt hz),map_zero]; rfl
abbrev mantra (x:Word G)(d:ℕ): poly Ξ:= lump (cut d (baseMark x))
lemma peek_mark (x:Word G)(hn:1<x.d) (h:x.d=2*d)(he:lody x=d) : peek P (mantra x d)=Labels.read (chunk P) ((labelledP x).val):= by
    let a:= x.S; let hP:= Vertex.normalized x.S x.H x.sound x.chosen x.axis; let T:= x.F
    have h₀ : cut d hP= cut d (baseMark x):= cut_thermal _ _ (base_rank x h)
    have he': Heat.Ray.clipped x.d hP=(labelledP x).val:= by
        have ht:= Heat.HueTag.shadow_eq (F:=x.F) hP (Grow.btw x); rw [show joint x.F hP= _ from Vertex.restores .., ← x.F.coords_basis, x.F.coords.symm_apply_apply] at ht; exact (congr_arg (fun p:Label G x.d=> p.val) ht).symm
    rw [mantra,←h₀,peer P hn,cut_view P (d:=d) ?_ h];
    · rw [Heat.Ray.ink_cut, Heat.Ray.cap_comm, show capRead _ _=_ from he', leafy.mp (show HC (labelledP x).val d from ?_)]
      exact he ▸ labelHC (k:=(x.F.grades x.axis).1) _ (x.F.pure x.axis)
    rw [Heat.Ray.ink_cut]; exact weightedHomogeneousComponent_mem ..
end YM.PositionX.Tri

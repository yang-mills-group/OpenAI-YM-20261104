import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land
import YM.FVAAlt2.Turn.Law
/-! Gallery of `Elect`: native Booked, H-invariant lift possible.
 Seeds in ℝ-linear span of full D-continuations at fixed starting count. Use
 ALL those (non-evanescent basis through weight & FREE), not assuming holomorphic
 emissions with inequivalent leading rows are allowed. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Motions
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum Outlook
open Mach Motif Literal Lifting Local.Physical Pole Halo Surf
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge}{B: Deck G}{P:Type} [AddCommGroup P] [Module ℂ P] {i:ℂ}{m n k:ℕ}{h x:ℝ}
variable (s t:Signed)
abbrev Γx (s:Signed):= hand s⁻¹
abbrev μs (G:Gauge)(s:Signed):= motion G (Γx s)
lemma trail_s : march ( hand s ) ( hand t )=hand (t*s):= eqSpin _ _ fun x=>( Signed.act_mul t s (R:=ℝ) x ).symm
lemma anti_mu (T:Mob G): μs G s (μs G t T)= μs G (s*t) T := by unfold μs Γx; rw [← motion_C,trail_s,mul_inv_rev]
lemma hand_back : ( hand s⁻¹ ).back=hand s:= eqSpin _ _ (fun x=> by apply (hand s⁻¹).turn.injective; rw [Spin.front]; exact (Signed.inv_act s x).symm )
lemma identity_motor : hand (1:Signed)=noneS 0:= eqSpin (hand 1) (noneS 0) (fun x=> Signed.act_one (R:=ℝ) x)
lemma tone_z (T:Mob G): μs G 1 T=T:=by unfold μs Γx; rw [inv_one,identity_motor,motion_Z]
local notation "X"=> Γx s
set_option quotPrecheck false
local notation "U" n=> Surf.orbit ((Γx s).arch (Nat.zero_le n)) G
abbrev Flip (s:Signed)(i:Axis): ℝ:= cross (s.flip i) true
lemma orient_spec (i:Axis) : (Flip s i:ℂ)=cross (s.flip i) true:=by unfold Flip; cases s.flip i <;> simp
lemma tender0(i:Axis)(j:Arts.L n): (U n).profile j (chair n i) =(if j=chair n (s.perm i) then (Flip s i:ℂ) else 0):= by
 let x:= (X).arch (Nat.zero_le n); change (x.profile j ( chair n i ):ℂ)= _; rw [x.dual]; unfold x; rw [arch_back,hand_back s, orient_spec]; rcases rangeA j (Nat.zero_le n) with ⟨k,rfl⟩| ⟨k,rfl⟩
 · unfold chair; rw [Spin.ray_taller _ _, hand_s]; simp only [EmbeddingLike.apply_eq_iff_eq]; congr 1; exact propext eq_comm
 unfold chair; rw [Spin.ray_away _ _,Complex.ofReal_zero]; exact Eq.symm (if_neg (nowhere (Nat.zero_le _) _ k).symm)
lemma turnsChair (i:Axis)(F:Arts.L n→ P): ∑ j:Arts.L n, (U n).profile j (chair n i) • F j=(Flip s i:ℂ) • F (chair n (s.perm i)):= by simp_rw [tender0,ite_smul,zero_smul]; simp
abbrev polarity (a:List Axis): ℝ:= (a.map (Flip s)).prod
def changes (w:Plaq): Plaq:= ⟨s.perm w.i,s.perm w.j, w.jets.map s.perm⟩
private theorem use_D (z:ℂ)(i j:Axis)(l:List Axis) : (U n).air (Pole G n i j z l) = (↑(polarity s (i::j::l)):ℂ) • Pole G n (s.perm i) (s.perm j) z (l.map s.perm):= by
    induction l with
    | nil=> rw [Pole,(U n).earth]; simp_rw [ turnsChair s ]; simp only [ List.map_nil,Pole ]; unfold polarity; simp [mul_smul]
    | cons a l ih=> rw [Pole,(U n).grip,turnsChair, ih, List.map_cons,Pole]; simp_rw [map_smul]; rw [smul_smul]; congr 1; unfold polarity; simp only [ List.map_cons,List.prod_cons ]; push_cast; ring
variable (G)
abbrev sale (a:Plaq):= polarity s (a.i::a.j::a.jets)
lemma leaf (a:Plaq)(i:G.ColorIndex)(z:ℂ): beam (flagS (Γx s|>.arch (Nat.zero_le n)) G) (Pole_leaf z a i)=(sale s a:ℂ) • Pole_leaf z (changes s a) i := congr_fun (use_D s z a.i a.j a.jets (G:=G) (n:=n)) i
variable {G}
lemma wing_M (f:Fin k→Plaq)(w:Lifting.Grid G k)(z:ℂ): μs G s (Pole.wing k f w z)= ((∏ i:Fin k,sale s (f i):ℝ):ℂ) • Pole.wing k ( changes s ∘ f ) w z:= by
 induction k with
 | zero=> simp only [ Fin.prod_univ_zero,Complex.ofReal_one,one_smul]; exact funext fun i=> (U i).fixC _
 | succ k ih=>
    let F:= f∘Fin.succ; let W:= w∘Fin.succ; funext i; change (U i).run (bite i G _ ( Pole.wing k F W z i )) = _; rw [(U i).prod, show (U i).run ( Pole_leaf z (f 0) (w 0) )= _ from leaf G s _ _ _, show (U i).run (Pole.wing k F W z i)= _ from congr_fun (ih F W) i, Fin.prod_univ_succ ]; simp only [LinearMap.smul_apply,map_smul,Pi.smul_apply]; push_cast; rw [ smul_smul, mul_comm ]; rfl -- inspect order
lemma walkV (f:Fin k→Plaq)(w:Lifting.Grid G k)(z:ℂ): μs G s (saint k f w z)=(∏ i:Fin k,sale s (f i):ℝ) • saint k (changes s ∘ f) w z:= by
   let A:=∏ i:Fin k,sale s (f i); rw [show (∏ i:Fin k,sale s (f i)) • saint _ _ _ _=(A:ℂ) • _ from Eq.symm ( IsScalarTower.algebraMap_smul ℂ A (saint k (changes s ∘ f) w z) ),saint, saint,map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul,wing_M]; exact smul_comm ..
theorem gallery_X {T:ℂ→Mob G} (h:T∈ Gallery G k n): μs G s ∘ T∈ Gallery G k n:= by
 refine Submodule.span_induction (p:=fun T _=> ((μs G s)∘T) ∈ Gallery G k _) ?_ ?_ ?_ ?_ h
 · rintro u ⟨l,w,rfl,rfl⟩; rw [show _∘_= (∏ i:Fin k,sale s (l i)) • saint k (changes s ∘ l) w from funext fun i=> walkV ..]; apply Submodule.smul_mem; apply Submodule.subset_span; refine ⟨_,_, ?_, rfl⟩; simp [changes,wage,Grit]
 · unfold Function.comp; simp only [Pi.zero_apply,map_zero]; exact Submodule.zero_mem _
 · intro u v _ _ hu hv; rw [show ⇑(μs G s) ∘ (u+v)=(⇑(μs G s)∘u)+(⇑(μs G s)∘v) from funext fun i=> map_add _ (u i) (v i)]; exact (Gallery ..).add_mem hu hv
 intro v T _ hv; let L: Mob G →ₗ[ℝ] Mob G:= (μs G s).restrictScalars ℝ; rw [show ⇑(μs G s) ∘ (v • T)= v • (⇑(μs G s) ∘ T) from funext fun i=> map_smul L v ( T i ) ]; exact Submodule.smul_mem _ _ hv

variable {T: Box (Mob G)} {W: Law G}
abbrev turnBo (G:Gauge)(s:Signed):= Boom 0 (μs G s)
abbrev turnW (G:Gauge)(s:Signed):= beam (flagS (m:=0) (Γx s) G)
theorem turned_E (h:Ele k n W T): Ele k n (turnW G s W) (turnBo G s T):= by
 let V:= turnBo G s; refine ⟨?_,?_⟩
 · unfold turnBo; simp_rw [linear_v]; exact gallery_X s h.1
 rw [ show turnBo G s T 0= _ from whole (μs G s) T 0 ]; unfold μs; rw [motion_zero,h.2]
lemma turn_gloss (W:Box ( Mob G)): gloss ( Literal.linear ( Mob G ) (turnBo G s W))=(mcoat G (Γx s)) ∘ gloss (Literal.linear ( Mob G ) W):= funext fun _=> funext fun _=> whole ..
end YM.MS.FVA.Motions
